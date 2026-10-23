#!/usr/bin/env python3
"""Bounded add-body proof-reuse tests; imports the existing snapshot supervisor."""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    'composition', ROOT / 'tests/hol_composition/run.py')
composition = importlib.util.module_from_spec(spec)
spec.loader.exec_module(composition)
PHASES = ('guards', 'canonical', 'named', 'authentication', 'factory', 'admission')


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError('Expected exactly one instrumentation anchor: ' + old)
    return source.replace(old, new, 1)


def instrument(source):
    source = replace_once(source, 'module Lean4hol_primitive : sig',
                          'module Add_body_probe : sig\n'
                          '  val add_body_typing : int -> Lean4hol_env.environment -> '
                          'Lean4hol.expr -> Lean4hol.expr -> thm -> thm')
    source = replace_once(source, '  module Env = Lean4hol_env', '''  module Env = struct
    include Lean4hol_env
    let check ?fuel env g b ty =
      add_body_probe_checks := (g,b,ty):: !add_body_probe_checks;
      Lean4hol_env.check ?fuel env g b ty
    let convert ?fuel env g a b ty =
      add_body_probe_converts := (g,a,b,ty,fuel):: !add_body_probe_converts;
      match !add_body_probe_conversion_override with
      | None -> Lean4hol_env.convert ?fuel env g a b ty
      | Some h -> Ok h
  end''')
    return '''(* Generated test-only observer/fault injector; never loaded by production. *)
let add_body_probe_checks : (Lean4hol.expr list * Lean4hol.expr * Lean4hol.expr) list ref = ref [];;
let add_body_probe_converts : (Lean4hol.expr list * Lean4hol.expr * Lean4hol.expr * Lean4hol.expr * int option) list ref = ref [];;
let add_body_probe_conversion_override : thm option ref = ref None;;
''' + source


def jobs():
    result = {phase: {
        'source_file': 'add_body_tests.ml',
        'markers': [r'ADD_BODY_TESTS_PASSED ' + phase + r' [0-9]+'],
        'limit': 180, 'options': {'ADD_BODY_PHASE': phase}}
        for phase in PHASES if phase != 'factory'}
    result['factory'] = {
        'source': 'use_file_raise_failure := true;;\nload_path := [Sys.getcwd()];;\n'
                  'needs "hol/primitive_contract_tests.ml";;\n',
        'markers': [r'HOL_PRIMITIVE_FACTORY_REQUIRED_PASSED',
                    r'HOL_PRIMITIVE_FACTORY_TESTS_PASSED [0-9]+'],
        'limit': 180, 'options': {'HOL_PRIMITIVE_SUITE': 'factory'}}
    return result


def prepare(destination):
    origins = composition.prepare_snapshot(destination)
    for relative in ('tests/hol_add_body/baseline/primitive_validation.ml',
                     'tests/hol_add_body/baseline/source-pins.json',
                     'tests/hol_add_body/run.py', 'tests/hol_add_body/test_runner.py'):
        source = ROOT / relative
        h = composition.digest(source)
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        if h != composition.digest(target) or h != composition.digest(source):
            raise RuntimeError('Source changed during copy: ' + relative)
        origins[relative] = h
    pins = json.loads((destination / 'tests/hol_add_body/baseline/source-pins.json').read_text())['source_sha256']
    if composition.digest(destination / 'tests/hol_add_body/baseline/primitive_validation.ml') != pins['hol/primitive_validation.ml']:
        raise RuntimeError('Baseline source hash mismatch')
    candidate = (destination / 'hol/primitive_validation.ml').read_text()
    baseline = (destination / 'tests/hol_add_body/baseline/primitive_validation.ml').read_text()
    (destination / 'hol/add_body_probe.ml').write_text(instrument(candidate))
    (destination / 'hol/add_body_baseline.ml').write_text(replace_once(
        baseline, 'module Lean4hol_primitive : sig', 'module Add_body_baseline : sig'))
    changed = [p for p, h in origins.items() if composition.digest(ROOT / p) != h]
    if changed:
        raise RuntimeError('Source changed during snapshot acquisition: ' + repr(changed))
    return origins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phases', nargs='*', choices=PHASES)
    parser.add_argument('--prepare-only', action='store_true', help='Create pinned snapshot without native HOL')
    args = parser.parse_args()
    selected = args.phases or list(PHASES)
    if len(set(selected)) != len(selected):
        parser.error('Repeated phase')
    report = ROOT / 'build/reports' / ('add-body-' +
        datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-' + str(os.getpid()))
    snapshot = report / 'snapshot'
    snapshot.mkdir(parents=True)
    origins = prepare(snapshot)
    provenance = {
        'origin_root': str(ROOT), 'origin_sha256': origins,
        'snapshot_sha256': composition.inventory(snapshot), 'selected': selected,
        'limit_seconds_per_test': 180, 'native_started': not args.prepare_only,
        'toolchain': str((ROOT / 'toolchain').resolve()),
        'boundary': 'Pinned project sources; shared toolchain and operating system are not hermetic.'}
    (report / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
    print('REPORT ' + str(report), flush=True)
    if args.prepare_only:
        return 0
    results = []
    for phase in selected:
        result = composition.run_job(snapshot, report, phase, jobs()[phase])
        results.append({'phase': phase, 'passed': result['passed']})
        summary = {'selected': selected, 'results': results,
                   'complete': len(results) == len(selected),
                   'passed': len(results) == len(selected) and all(r['passed'] for r in results)}
        (report / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
        if not result['passed']:
            return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
