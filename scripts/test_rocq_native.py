#!/usr/bin/env python3
"""Build and run bounded regressions against the local Rocq extraction.

Run build-rocq.sh first. This suite does not invoke Lean, use Arena verdicts,
or establish correspondence between the ordinary checker and Lean's logic.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts/toolchain-exec.sh"


def fingerprint(path):
    return {"sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "bytes": path.stat().st_size}


def source_snapshot():
    files = [p for directory in ("rocq", "frontend", "scripts")
             for p in (ROOT / directory).iterdir()
             if p.is_file() and p.suffix in (".v", ".ml", ".mli", ".py", ".sh")]
    files.append(ROOT / "tests/rocq/hint-policy-controls.json")
    return {str(p.relative_to(ROOT)): fingerprint(p) for p in sorted(files)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=240,
                        help="wall seconds per compile, link, or test process")
    parser.add_argument("--report-dir", type=Path)
    args = parser.parse_args()
    if not 0 < args.timeout < float("inf"):
        parser.error("timeout must be positive and finite")
    out = args.report_dir or ROOT / "build/reports" / (
        "rocq-native-" + time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()) + "-" + str(os.getpid()))
    out = out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    build = ROOT / "build/rocq-regressions"
    build.mkdir(parents=True, exist_ok=True)
    report = {"complete": False, "source_before": source_snapshot(), "steps": [], "suites": []}

    def save():
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(command, label, marker=None):
        index = len(report["steps"])
        log = out / f"{index:02d}-{label}.log"
        start = time.monotonic()
        timed_out = False
        with log.open("wb") as stream:
            process = subprocess.Popen([str(x) for x in command], cwd=ROOT,
                                       stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            def terminate():
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                return process.wait()
            try:
                code = process.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                code = terminate()
            except BaseException:
                terminate()
                raise
        output = log.read_text(errors="replace")
        found = marker is None or re.search(marker, output, flags=re.MULTILINE) is not None
        step = {"label": label, "command": [str(x) for x in command], "exit": code,
                "pid": process.pid, "reaped": True, "timed_out": timed_out,
                "seconds": time.monotonic() - start, "log": log.name,
                "log_fingerprint": fingerprint(log), "marker_found": found}
        report["steps"].append(step)
        save()
        if code != 0 or timed_out or not found:
            raise RuntimeError(f"{label} failed; inspect {log}")
        if marker is not None:
            report["suites"].append(label)
            print(output.strip(), flush=True)

    def ocaml(*args):
        return ["sh", TOOL, "ocamlfind", "ocamlopt", "-package", "yojson,zarith", *args]

    def extracted(module):
        run(ocaml("-c", "-o", build / (module + ".cmi"), ROOT / "rocq" / (module + ".mli")),
            "interface-" + module)
        run(ocaml("-I", build, "-c", "-o", build / (module + ".cmx"),
                  ROOT / "rocq" / (module + ".ml")), "extract-" + module)

    def compile_source(module):
        source = ROOT / "frontend" / (module + ".ml")
        if module == "core_regression":
            source = ROOT / "rocq/core_regression.ml"
        run(ocaml("-w", "+8+11", "-warn-error", "+8+11", "-I", build,
                  "-c", "-o", build / (module + ".cmx"), source), "source-" + module)

    def suite(name, dependencies, marker, arguments=()):
        compile_source(name)
        binary = build / name
        run(ocaml("-linkpkg", "-I", build,
                  *[build / (m + ".cmx") for m in [*dependencies, name]], "-o", binary),
            "link-" + name)
        run([binary, *arguments], name, marker)

    try:
        extracted("lean_arena")
        for module in ("wire", "replay", "rocq_adapter", "dag_adapter"):
            compile_source(module)
        compile_source("replay_reference")
        suite("test_replay_differential", ["wire", "replay", "replay_reference"],
              r"^REPLAY_DIFFERENTIAL_PASS 2006$")
        base = ["wire", "replay", "lean_arena", "rocq_adapter", "dag_adapter"]
        suite("test_dag_admission", base, r"^\d+ synthetic exact comparisons passed$")
        suite("test_dag_theorem_opaque", base, r"comparisons")
        suite("test_indexed_dag", base, r"comparisons")
        compile_source("full_result")
        suite("test_string_runtime", [*base, "full_result"],
              r'^PASS new: 14 admitted gates; 22 observations; 36 prepared conversion full comparisons; 24 indexed theorem full comparisons$', ["new"])
        compile_source("persistent_adapter")
        suite("persistent_adapter_tests", [*base, "persistent_adapter"],
              r"^adapter_assertions=664 accepted_batches=481 rejected_batches=15 declined_batches=74$")
        suite("test_hints", [*base, "full_result", "persistent_adapter"],
              r"^HINTS_NATIVE_PASS assertions=3217$")
        suite("test_hint_callbacks", base,
              r"^HINT_CALLBACKS_PASS priority_vectors=14 guard_requirements_passed=23 documented_unimplemented=1 extra_controls=10$",
              [ROOT / "tests/rocq/hint-policy-controls.json"])
        suite("test_nat_probe_callbacks", base,
              r"^NAT_PROBE_CALLBACKS_PASS suites=9 assertions=1199$")
        extracted("eager_policy_native")
        suite("test_eager_policy_callbacks", ["eager_policy_native"],
              r"^EAGER_POLICY_CALLBACKS_PASS suites=16 assertions=11678$")
        extracted("guard_order_native")
        suite("test_guard_order_callbacks", ["guard_order_native"],
              r"^GUARD_ORDER_CALLBACKS_PASS assertions=1739 inactive_shapes=26 shared_depth=50 modes=2 implementations=2$")
        extracted("whnf_policy_native")
        suite("test_whnf_policy_callbacks", ["whnf_policy_native"],
              r"^WHNF_POLICY_CALLBACKS_PASS assertions=5762$")
        extracted("whnf_production_native")
        suite("test_whnf_production_callbacks", ["whnf_production_native"],
              r"^WHNF_PRODUCTION_CALLBACKS_PASS implementations=2 builders=2 modes=2 assertions=720$")
        extracted("persistent_tests_native")
        suite("persistent_tests", ["persistent_tests_native"],
              r"^assertions=129520 full_result_comparisons=2984 lookup_comparisons=126212 step_accept=666 step_reject=1924 step_decline=134$")
        suite("persistent_stream_tests", ["persistent_tests_native"],
              r"^PASS persistent_stream: assertions=52776 full_results=1448 checked_steps=1332 lookups=51126 observations=44 changed_per_hash=7 nested_positives=4 rollbacks=38$")
        for module, test, marker, arguments in (
            ("depth_native", "test_depth_index", r"exact depth/linear-cache comparisons", []),
            ("metadata_native", "metadata_tests", r"positive_admission_gates=9", []),
            ("cheap_header_native", "cheap_header_tests", r"zero_preparation_probes=\d+", []),
            ("string_parity", "parity_ordinary", r"^PASS candidate: 14 positive gates; 22 observations$", ["candidate"]),
            ("lean_core", "core_regression", r"4096", []),
        ):
            extracted(module)
            suite(test, [module], marker, arguments)
        extracted("universe_native")
        suite("test_universe_semantics", ["universe_native"],
              r"^UNIVERSE_SEMANTICS_PASS assertions=626207 levels=1260 valuations=16 accepted=1343 rejected=2900 declined=2057$")
        extracted("universe_complete_native")
        suite("test_universe_completeness", ["universe_complete_native"],
              r"^UNIVERSE_COMPLETENESS_PASS assertions=786581 witnesses=126288 atoms=92 lists=277 levels=180 valuations=27$")
        extracted("universe_instantiation_native")
        suite("test_universe_instantiation", ["universe_instantiation_native"],
              r"^UNIVERSE_INSTANTIATION_PASS assertions=3366071 levels=336 parameter_lists=7 replacement_lists=10 valuations=27 positive_le=7952 positive_eq=2408$")
        extracted("universe_expression_native")
        suite("test_universe_expression", ["universe_expression_native"],
              r"^UNIVERSE_EXPRESSION_PASS assertions=7264342 expressions=3290 configurations=24$")
        report["source_after"] = source_snapshot()
        if report["source_before"] != report["source_after"]:
            raise RuntimeError("Sources changed during native regression run")
        report["complete"] = True
    finally:
        save()
        print(f"Report: {out / 'report.json'}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
