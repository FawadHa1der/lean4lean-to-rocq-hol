#!/usr/bin/env python3
"""Focused repaired-main controls; the long historical matrix is explicit opt-in."""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve()
spec = importlib.util.spec_from_file_location('reflection_driver', HERE.with_name('test-hol-reflection.py'))
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
original_inventory = driver.inventory
original_fixture_stages = driver.fixture_stages


def inventory(root=driver.ROOT):
    result = original_inventory(root)
    for rel in ('scripts/test-hol-unified.py',
                'tests/hol_reflection/test_unified_runner.py',
                'tests/hol_reflection/unified_synthetic_backend.py'):
        result[rel] = driver.sha(root / rel)
    return result


def fixture_stages(fixture, ready):
    result = []
    if fixture == 'unified_tests.ml':
        result.append(dict(stage='setup-nat-dependencies', kind='setup',
            command='needs "tests/hol_reflection/nat_instantiation_tests.ml";;',
            marker=r'NAT_INSTANTIATION_SETUP_READY\s*'))
    result += original_fixture_stages(fixture, ready)
    return result


def plan(groups):
    if groups == ['focused']:
        phases = ['admit', 'base', 'ite']
        phases += [f'default-{i}-{d}' for i, d in ((0, 0), (1, 0), (0, 1), (1, 1))]
        phases += ['prepared-flags', 'typed-sources', 'controls', 'invariants']
        return 'prepared_bool_tests.ml', 'UNIFIED_SETUP_READY', [
            (p, 'Lean4hol_prepared_bool_tests', 'UNIFIED',
             'preparation' if p == 'admit' else 'negative' if p in ('typed-sources', 'controls')
             else 'audit' if p == 'invariants' else 'capability') for p in phases]
    assert groups == ['unified']
    stages = []
    def nat(phase, composition=False):
        stages.append((phase, 'Lean4hol_nat_composition_tests' if composition else
                       'Lean4hol_nat_tests', 'NAT', 'preparation'))
    def unified(phase, kind='preparation'):
        stages.append((phase, 'Lean4hol_unified_tests', 'UNIFIED', kind))
    for phase in ('ble ble-diag nat-le le-class le-projection le-instance zero-le succ-le '
                  'le-true ble-step ble-of-le le-false dec-le').split():
        nat(phase)
    unified('seal-env')
    for which in ('d2', 'd1'):
        if which == 'd1':
            for phase in ('dec-infer gadget-infer 1').split():
                nat('le-' + phase)
            for phase in ('seed close-1 close-2 close-3 close-4 arg-1 arg-2 arg-3 arg-4 '
                          'wrapper-init wrapper-1 wrapper-2 wrapper-3 proof-link delta finish').split():
                nat('le-' + phase, True)
            unified('nat-capture', 'capability')
        for kind in ('ite', 'dite'):
            for n in range(2 if kind == 'ite' else 5):
                unified(f'{which}-{kind}-type-{n}')
            for branch in ('true', 'false'):
                unified(f'{which}-{kind}-{branch}-body')
                unified(f'{which}-{kind}-{branch}-close')
            unified(f'{which}-{kind}-whole', 'capability')
    unified('nat-dispatch', 'capability')
    for ite, dite in ((0, 0), (1, 0), (0, 1), (1, 1)):
        unified(f'bool-default-{ite}-{dite}', 'capability' if dite == 0 else 'negative')
    unified('bool-prepared', 'capability')
    for kind in ('ite', 'dite'):
        for branch in ('true', 'false'):
            unified(f'bad-{kind}-{branch}', 'negative')
    unified('controls', 'negative')
    unified('invariants', 'audit')
    return 'unified_tests.ml', 'UNIFIED_SETUP_READY', stages


driver.inventory = inventory
driver.fixture_stages = fixture_stages
driver.plan = plan
driver.GROUPS = ('focused', 'unified')
if __name__ == '__main__':
    if len(sys.argv) == 1:
        sys.argv.append('focused')
    raise SystemExit(driver.main())
