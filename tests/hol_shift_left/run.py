#!/usr/bin/env python3
"""Bounded opt-in shiftLeft gates; prepare-only never launches HOL."""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('composition', ROOT / 'tests/hol_composition/run.py')
composition = importlib.util.module_from_spec(spec)
spec.loader.exec_module(composition)
PHASES = ('general', 'empty', 'nat-context', 'dependent-context', 'large-and-budget',
          'allocation-controls', 'contract-guards', 'primitive-import', 'authentication', 'wrappers')


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError('Expected one test instrumentation anchor: ' + old)
    return source.replace(old, new, 1)


PROBE_PREFIX = '''(* Test-only observer; cannot manufacture a HOL theorem. *)
let shift_left_probe_numeric_inputs : term list ref = ref [];;
let shift_left_probe_require_zero = ref false;;
let shift_left_probe_forbid_numeric = ref false;;
let shift_left_probe_num_reduce tm =
  shift_left_probe_numeric_inputs := tm :: !shift_left_probe_numeric_inputs;
  if !shift_left_probe_forbid_numeric then
    failwith "numeral reduction reached after a preflight refusal";
  if !shift_left_probe_require_zero && not(aconv tm `0`) then
    failwith "zero product was not eliminated before numeral reduction";
  NUM_REDUCE_CONV tm;;
'''


def evaluation_probe(source):
    source = replace_once(source, 'module Lean4hol_derived_shift_left : sig',
                          'module Shift_left_evaluation_probe : sig')
    source = replace_once(source,
        'let arithmetic=(REWRITE_CONV [MULT_CLAUSES] THENC NUM_REDUCE_CONV) expression in',
        'let arithmetic=(REWRITE_CONV [MULT_CLAUSES] THENC shift_left_probe_num_reduce) expression in')
    return PROBE_PREFIX + source


def jobs():
    return {phase: {
        'source_file': 'shift_left_general_tests.ml' if phase == 'general' else 'shift_left_cases_tests.ml',
        'markers': [r'SHIFT_LEFT_DERIVED_PASSED ' + phase + r' [0-9]+'],
        'limit': 180, 'options': {'SHIFT_LEFT_PHASE': phase}}
        for phase in PHASES}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phases', nargs='*')
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    selected = args.phases or list(PHASES)
    if len(set(selected)) != len(selected) or set(selected) - set(PHASES):
        parser.error('Unknown or repeated phase')
    report = ROOT / 'build/reports' / ('shift-left-' +
        datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-' + str(os.getpid()))
    snapshot = report / 'snapshot'
    snapshot.mkdir(parents=True)
    origins = composition.prepare_snapshot(snapshot)
    for name in ('run.py', 'test_offline.py', 'budget_tests.ml'):
        relative = 'tests/hol_shift_left/' + name
        source = ROOT / relative
        expected = composition.digest(source)
        destination = snapshot / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        if composition.digest(source) != expected or composition.digest(destination) != expected:
            raise RuntimeError('Source changed during acquisition')
        origins[relative] = expected
    if any(composition.digest(ROOT / p) != h for p, h in origins.items()):
        raise RuntimeError('Source changed during snapshot acquisition')
    production = snapshot / 'hol/derived_shift_left.ml'
    probe = snapshot / 'hol/shift_left_evaluation_probe.ml'
    probe.write_text(evaluation_probe(production.read_text()))
    provenance = {'origin_root': str(ROOT), 'origin_sha256': origins,
                  'snapshot_sha256': composition.inventory(snapshot), 'selected': selected,
                  'native_started': not args.prepare_only, 'limit_seconds_per_group': 180,
                  'generated_test_probe': {'path': 'hol/shift_left_evaluation_probe.ml',
                      'sha256': composition.digest(probe), 'production_sha256': composition.digest(production),
                      'changes': 'Test module rename and observing arithmetic conversion only; production unchanged.'},
                  'boundary': 'Pinned project sources; shared toolchain and OS are not hermetic.'}
    (report / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
    print('REPORT ' + str(report), flush=True)
    if args.prepare_only:
        return 0
    results = []
    for phase in selected:
        result = composition.run_job(snapshot, report, phase, jobs()[phase])
        results.append({'phase': phase, 'passed': result['passed']})
        summary = {'selected': selected, 'results': results, 'complete': len(results) == len(selected),
                   'passed': len(results) == len(selected) and all(r['passed'] for r in results)}
        (report / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
        if not result['passed']:
            return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
