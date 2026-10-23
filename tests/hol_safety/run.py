#!/usr/bin/env python3
"""Separate opt-in safety gates, frozen sources, unchanged 180s limits."""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('composition', ROOT / 'tests/hol_composition/run.py')
composition = importlib.util.module_from_spec(spec)
# The shared runner imports sibling helpers; do not register safety jobs there.
sys.path.insert(0, str(ROOT / 'tests/hol_composition'))
try:
    spec.loader.exec_module(composition)
finally:
    sys.path.pop(0)
FOCUSED = ('general', 'single', 'mutual', 'references', 'authentication', 'shape', 'atomicity', 'wrappers')
LIMIT = 180
LOAD_PHASE_FILE = 'tests/hol_safety/drivers/load_phases.ml'
LOAD_MARKERS = ('SAFETY_LOAD_PHASE transport ordinary', 'SAFETY_LOAD_PHASE proofs jrh',
                'SAFETY_LOAD_PHASE frontend ordinary', 'SAFETY_LOAD_PHASE adapter jrh')
LOAD_ROOTS = ('build/frontend/wire.cmo', 'build/frontend/replay.cmo',
              'build/frontend/hol_input.cmo', 'build/frontend/hol_safety_input.cmo',
              'hol/environment.ml', 'hol/primitive_validation.ml', 'hol/text_validation.ml',
              'hol/raw_indexed_admission.ml', 'hol/safety_admission.ml',
              'frontend/hol_check.ml', 'frontend/hol_safety_check.ml')
PRODUCTION = ('hol/environment.ml', 'hol/safety_syntax.ml', 'hol/safety_admission.ml',
              'frontend/hol_safety_input.ml', 'frontend/hol_safety_check.ml')


def jobs():
    result = {phase: {'source_file': 'safety_tests.ml', 'limit': LIMIT,
                     'markers': [r'SAFETY_DEFINITIONS_PASSED ' + phase + r' [0-9]+ closed_exact unchanged_axioms rules29_11'],
                     'options': {'SAFETY_GROUP': phase}} for phase in FOCUSED}
    result['arena'] = {'source_file': 'safety_arena_tests.ml', 'limit': LIMIT,
        'markers': [r'SAFETY_ARENA_REJECT 140_falseFromUnsafe prefix_checked=2 line=22 exact_closed forbidden_closed retained_loop',
                    r'SAFETY_ARENA_REJECT 141_falseFromPartial prefix_checked=2 line=22 exact_closed forbidden_closed retained_loop',
                    r'SAFETY_ARENA_PASSED 17 unchanged_axioms'], 'options': {}}
    for job in result.values():
        job['markers'] = list(LOAD_MARKERS) + job['markers']
    return result


def save(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def runtime_identity():
    hol = subprocess.check_output(['sh', 'scripts/toolchain-exec.sh', 'hol.sh', '-dir'],
                                  cwd=ROOT, text=True).strip()
    code = ('import os,json,shutil;print(json.dumps({"env":{k:os.environ.get(k) for k in ' + repr(
        ['OPAMROOT', 'OPAMSWITCH', 'OCAMLLIB', 'CAML_LD_LIBRARY_PATH', 'OCAML_TOPLEVEL_PATH', 'PATH']) +
        '},"hol_launcher":shutil.which("hol.sh")}))')
    environment = json.loads(subprocess.check_output(
        ['sh', 'scripts/toolchain-exec.sh', sys.executable, '-c', code], cwd=ROOT, text=True))
    library = Path(hol).parent
    roots = [Path(hol)] + [library / name for name in
        ('ocaml', 'camlp5', 'camlp-streams', 'zarith', 'yojson', 'toplevel', 'stublibs')]
    files = {}
    for root in roots:
        if root.is_dir():
            for p in sorted(root.rglob('*')):
                if p.is_file():
                    files[str(p)] = composition.digest(p)
    launcher = Path(environment['hol_launcher'])
    files[str(launcher)] = composition.digest(launcher)
    identity = {'hol_directory': hol, 'ocaml_hol': str(Path(hol) / 'ocaml-hol'),
                'resolved_ocaml_hol': str((Path(hol) / 'ocaml-hol').resolve()),
                'environment': environment, 'files': files,
                'boundary': 'Actual launcher and HOL/OCaml/library source-bytecode closure pinned; OS/shared dylibs not hermetic.'}
    return identity


def runtime_held(identity):
    changed = []
    for path, digest in identity['files'].items():
        p = Path(path)
        if not p.is_file() or composition.digest(p) != digest:
            changed.append(path)
    return changed


def prepare(snapshot):
    origins = composition.prepare_snapshot(snapshot)

    def copy(relative, target=None):
        source = ROOT / relative
        before = composition.digest(source)
        destination = snapshot / (target or relative)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        if composition.digest(source) != before or composition.digest(destination) != before:
            raise RuntimeError('Source changed during safety capture: ' + relative)
        origins[relative] = before

    for extension in ('cmo', 'cmi'):
        copy('build/frontend/hol_safety_input.' + extension)
    for relative in ('tests/hol_safety/run.py', 'tests/hol_safety/test_offline.py',
                     'tests/hol_safety/helper_contract.py', 'tests/hol_safety/test_maintenance.py',
                     'tests/hol_safety/frontend_tests.ml'):
        copy(relative)
    copy('tests/hol_safety/drivers/safety_tests.ml', 'safety_tests.ml')
    copy('tests/hol_safety/drivers/arena_tests.ml', 'safety_arena_tests.ml')
    copy(LOAD_PHASE_FILE, 'safety_load_phases.ml')
    for name in ('140_falseFromUnsafe', '141_falseFromPartial'):
        copy('arena/corpus/tutorial/' + name + '.ndjson')
    if any(composition.digest(ROOT / p) != h for p, h in origins.items()):
        raise RuntimeError('Private source changed before hold release')
    return origins


def assertions(log, phase):
    if phase == 'arena':
        pattern = r'(?m)^(?:#\s*)?SAFETY_ARENA_ASSERT (\d+) (true|false) ([^\r\n]*)$'
    else:
        pattern = r'(?m)^(?:#\s*)?SAFETY_ASSERT ' + re.escape(phase) + r' (\d+) (true|false) ([^\r\n]*)$'
    found = [{'index': int(i), 'passed': passed == 'true', 'label': label}
             for i, passed, label in re.findall(pattern, log)]
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    report = ROOT / 'build/reports' / ('safety-native-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-' + str(os.getpid()))
    snapshot = report / 'snapshot'
    snapshot.mkdir(parents=True)
    origins = prepare(snapshot)
    runtime = runtime_identity()
    save(report / 'runtime-before.json', runtime)
    provenance = {'origin_root': str(ROOT), 'origin_sha256': origins,
                  'snapshot_sha256': composition.inventory(snapshot),
                  'production_sha256': {p: composition.digest(snapshot / p) for p in PRODUCTION},
                  'native_started': not args.prepare_only, 'origin_hold_released': True,
                  'phases': list(FOCUSED) + ['arena'], 'limit_seconds': LIMIT,
                  'loading': {'input_mode': 'separate interactive top-level phrases',
                              'source_file': LOAD_PHASE_FILE, 'phase_markers': LOAD_MARKERS,
                              'root_sha256': {p: composition.digest(snapshot / p) for p in LOAD_ROOTS},
                              'external_bytecode': ['zarith.cma', 'yojson.cma', 'unix.cma'],
                              'external_provenance': 'runtime-before.json'},
                  'arena_gate': 'All eight focused phases must pass first, on this exact frozen snapshot.'}
    save(report / 'provenance.json', provenance)
    print('REPORT ' + str(report), flush=True)
    print('PRIVATE_ORIGIN_HOLD_RELEASED', flush=True)
    if args.prepare_only:
        save(report / 'prepare-only.json', {'native_runs': 0, 'runtime_file_count': len(runtime['files'])})
        return 0
    results = []
    for phase in list(FOCUSED) + ['arena']:
        if phase == 'arena' and (len(results) != len(FOCUSED) or not all(r['passed'] for r in results)):
            raise RuntimeError('Arena cannot run before every focused gate passes')
        drift = runtime_held(runtime)
        if drift:
            save(report / 'infrastructure-stop.json', {'phase': phase, 'runtime_drift': drift})
            return 2
        job = dict(jobs()[phase])
        source = (snapshot / job.pop('source_file')).read_text()
        job['source'] = ('Printf.printf "SAFETY_RUNTIME_ID %s\\nSAFETY_SNAPSHOT_ID %s\\n%!" Sys.executable_name (Sys.getcwd());;\n' +
                         (snapshot / 'safety_load_phases.ml').read_text() + '\n' + source)
        result = composition.run_job(snapshot, report, phase, job)
        log = (report / (phase + '.log')).read_text(errors='replace')
        observed = assertions(log, phase)
        identity_ok = ('SAFETY_RUNTIME_ID ' + runtime['ocaml_hol']) in log and ('SAFETY_SNAPSHOT_ID ' + str(snapshot)) in log
        ordinal_ok = [r['index'] for r in observed] == list(range(1, len(observed) + 1))
        complete_marker = re.search(r'SAFETY_(?:DEFINITIONS_PASSED ' + re.escape(phase) + r'|ARENA_PASSED) (\d+)', log)
        counts_match = complete_marker is not None and int(complete_marker.group(1)) == len(observed)
        loading_observed = re.findall(r'(?m)^(?:#\s*)?(SAFETY_LOAD_PHASE [^\r\n]+)$', log)
        loading_ok = loading_observed == list(LOAD_MARKERS)
        drift = runtime_held(runtime)
        audit = {'phase': phase, 'assertions': observed, 'assertions_passed': sum(r['passed'] for r in observed),
                 'assertions_failed': sum(not r['passed'] for r in observed),
                 'identity_ok': identity_ok, 'ordinal_ok': ordinal_ok, 'counts_match_marker': counts_match,
                 'loading_phases': loading_observed, 'loading_order_ok': loading_ok,
                 'runtime_drift': drift, 'native_result_passed': result['passed'],
                 'passed': result['passed'] and identity_ok and loading_ok and ordinal_ok and counts_match and not drift and
                           bool(observed) and all(r['passed'] for r in observed),
                 'cleanup_verified': result['reaped'] and result['process_group_absent'],
                 'source_held': result['before'] == result['after'],
                 'input_sha256': result['input_sha256'], 'log_sha256': result['log_sha256'],
                 'stdout_stderr': 'Combined complete logfile retained; no truncation by harness.',
                 'seconds': result['seconds'], 'limit_seconds': LIMIT}
        save(report / (phase + '-audit.json'), audit)
        results.append(audit)
        summary = {'results': results, 'all_focused_passed': len(results) >= len(FOCUSED) and
                   all(r['passed'] for r in results[:len(FOCUSED)]),
                   'arena_attempted': any(r['phase'] == 'arena' for r in results),
                   'complete': len(results) == len(FOCUSED) + 1,
                   'passed': len(results) == len(FOCUSED) + 1 and all(r['passed'] for r in results)}
        save(report / ('progress-' + str(len(results)) + '.json'), summary)
        print(json.dumps({'phase': phase, 'passed': audit['passed'], 'assertions': len(observed),
                          'cleanup_verified': audit['cleanup_verified']}), flush=True)
        if not audit['passed']:
            save(report / 'first-native-failure.json', summary)
            return 1
    save(report / 'complete.json', summary)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
