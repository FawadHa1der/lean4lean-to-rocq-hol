#!/usr/bin/env python3
"""Run genuine HOL composition tests in a bounded, source-pinned snapshot."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

import early_variants

ROOT = Path(__file__).resolve().parents[2]
SUITE = ROOT / 'tests/hol_composition'
ERROR = re.compile(r'(?m)^.*(?:Error:|Exception:|Parse error|Lexing error|'
                   r'Error in included file|Cannot find file|Fatal error:).*$')
FULL_FILES = ['tests', 'nat_literal_tests', 'family_tests', 'indexed_tests',
              'projection_core_tests', 'projection_tests', 'structure_tests',
              'quotient_tests', 'primitive_contract_tests', 'text_tests',
              'string_syntax_tests', 'string_literal_tests', 'string_quotient_tests',
              'structure_major_tests', 'structure_string_tests', 'reflexive_tests',
              'validation_tests']
FULL_MARKERS = ['CORE', 'ADMISSION', 'ENVIRONMENT', 'INDUCTIVE', 'NAT_LITERAL',
                'FAMILY', 'INDEXED', 'PROJECTION_CORE', 'PROJECTION', 'STRUCTURE',
                'QUOTIENT', 'PRIMITIVE_POW_FACTORY', 'TEXT_PRIMITIVE', 'STRING_SYNTAX',
                'STRING_LITERAL', 'STRING_QUOTIENT', 'STRUCTURE_MAJOR',
                'STRUCTURE_STRING_EXCLUSION', 'REFLEXIVE', 'ITERATIVE_VALIDATION']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(root):
    return {str(p.relative_to(root)): digest(p) for p in sorted(root.rglob('*'))
            if p.is_file() and not p.is_symlink() and '__pycache__' not in p.parts}


def marker(name):
    return r'HOL_' + name + r'_TESTS_PASSED [0-9]+'


def jobs():
    result = {}
    result['bool-general'] = {
        'source': 'needs "bool_general_tests.ml";;\nrun_bool_general ();;\n',
        'markers': [r'COMPOSED_WORK_PASS bool-general [0-9]+'],
        'limit': 180, 'options': {}}
    for operation in ('beq', 'ble'):
        for phase in ('empty', 'nat-context', 'dependent', 'beta', 'let', 'named',
                      'guards', 'missing', 'impostor-zz', 'impostor-zs',
                      'impostor-sz', 'impostor-ss', 'finite'):
            tag = 'bool-' + operation + '-' + phase
            result[tag] = {
                'source': 'needs "bool_cases_tests.ml";;\nrun_bool_cases ' +
                          json.dumps(operation) + ' ' + json.dumps(phase) + ';;\n',
                'markers': [r'COMPOSED_WORK_PASS ' + tag + r' [0-9]+'],
                'limit': 180, 'options': {}}
    for group in ('differential', 'guards', 'benchmark'):
        result['closed-computation-' + group] = {
            'source_file': 'closed_computation_tests.ml',
            'markers': [r'CLOSED_COMPUTATION_NATIVE_PASS ' + group + r' [0-9]+'],
            'limit': 180, 'options': {'CLOSED_GROUP': group}}
    result.update({
        "hadd-119": {
            "source_file": "hadd_function_files.ml",
            "markers": [
                "PRIVATE_INDEXED_FILE_DONE 119 exact_original_history three_invariants tamper_decline unchanged_axioms"
            ],
            "limit": 180,
            "options": {
                "COMPOSE_GROUP": "119"
            }
        },
        "hadd-120": {
            "source_file": "hadd_function_files.ml",
            "markers": [
                "PRIVATE_INDEXED_FILE_DONE 120 exact_original_history three_invariants tamper_decline unchanged_axioms"
            ],
            "limit": 180,
            "options": {
                "COMPOSE_GROUP": "120"
            }
        },
        "hadd-hadd": {
            "source_file": "hadd_positive_tests.ml",
            "markers": [
                "PRIVATE_POSITIVE_DONE hadd exact_original_history three_invariants tamper_decline unchanged_axioms"
            ],
            "limit": 180,
            "options": {
                "COMPOSE_GROUP": "hadd"
            }
        },
        "hadd-raw055": {
            "source_file": "hadd_positive_tests.ml",
            "markers": [
                "PRIVATE_POSITIVE_DONE raw055 exact_original_history three_invariants tamper_decline unchanged_axioms"
            ],
            "limit": 180,
            "options": {
                "COMPOSE_GROUP": "raw055"
            }
        },
        "hadd-domain": {
            "source_file": "hadd_control_tests.ml",
            "markers": [
                "PRIVATE_TYPED altered_field_domain closed_formation",
                "PRIVATE_DECLINE altered_domain_fixed_anchor [^\\r\\n]+",
                "PRIVATE_DECLINE altered_domain_original_recursor [^\\r\\n]+",
                "PRIVATE_CONTROL_DONE domain no_resource_negatives unchanged_axioms"
            ],
            "limit": 180,
            "options": {
                "COMPOSE_GROUP": "domain"
            }
        },
        "hadd-universes": {
            "source_file": "hadd_control_tests.ml",
            "markers": [
                "PRIVATE_TYPED swapped_result_universes_and_parameters closed_formation",
                "PRIVATE_DECLINE exact_result_universes [^\\r\\n]+",
                "PRIVATE_DECLINE candidate_uniform_result [^\\r\\n]+",
                "PRIVATE_DECLINE polymorphic_field_universe_bound [^\\r\\n]+",
                "PRIVATE_CONTROL_DONE universes no_resource_negatives unchanged_axioms"
            ],
            "limit": 180,
            "options": {
                "COMPOSE_GROUP": "universes"
            }
        },
        "hadd-metadata": {
            "source_file": "hadd_control_tests.ml",
            "markers": [
                "PRIVATE_TYPED original_types_before_metadata_tamper closed_formation",
                "PRIVATE_DECLINE wrong_field_count [^\\r\\n]+",
                "PRIVATE_DECLINE recursor_universe_parameter_order [^\\r\\n]+",
                "PRIVATE_CONTROL_DONE metadata no_resource_negatives unchanged_axioms"
            ],
            "limit": 180,
            "options": {
                "COMPOSE_GROUP": "metadata"
            }
        },
        "hadd-rhs": {
            "source_file": "hadd_control_tests.ml",
            "markers": [
                "PRIVATE_TYPED rhs_beta_wrapper closed_inference_and_conversion",
                "PRIVATE_DECLINE typed_computational_rhs_shape [^\\r\\n]+",
                "PRIVATE_CONTROL_DONE rhs no_resource_negatives unchanged_axioms"
            ],
            "limit": 180,
            "options": {
                "COMPOSE_GROUP": "rhs"
            }
        },
        "hadd-erased": {
            "source_file": "hadd_control_tests.ml",
            "markers": [
                "PRIVATE_DECLINE illtyped_erased_beta_formation [^\\r\\n]+",
                "PRIVATE_DECLINE illtyped_erased_beta [^\\r\\n]+",
                "PRIVATE_DECLINE illtyped_erased_let_formation [^\\r\\n]+",
                "PRIVATE_DECLINE illtyped_erased_let [^\\r\\n]+",
                "PRIVATE_CONTROL_DONE erased no_resource_negatives unchanged_axioms"
            ],
            "limit": 180,
            "options": {
                "COMPOSE_GROUP": "erased"
            }
        },
        "hadd-forward": {
            "source_file": "hadd_control_tests.ml",
            "markers": [
                "PRIVATE_TYPED forward_constructor_in_final_environment closed_formation",
                "PRIVATE_DECLINE forward_header_only_formation [^\\r\\n]+",
                "PRIVATE_DECLINE forward_bridge_guard [^\\r\\n]+",
                "PRIVATE_DECLINE forward_raw_admission [^\\r\\n]+",
                "PRIVATE_CONTROL_DONE forward no_resource_negatives unchanged_axioms"
            ],
            "limit": 180,
            "options": {
                "COMPOSE_GROUP": "forward"
            }
        },
        "hadd-counterexample": {
            "source_file": "hol/hadd_counterexample_tests.ml",
            "markers": [
                "PRIVATE_COUNTEREXAMPLE_DONE old_bridge_accepts new_admission_declines exact_closed unchanged_axioms"
            ],
            "limit": 180,
            "options": {}
        },
        "hadd-raw-rhs": {
            "source_file": "hadd_function_controls.ml",
            "markers": [
                "INDEXED_POSITIVE authentic119_control exact_closed",
                "INDEXED_DECLINE rhs_computational_tamper [^\\r\\n]+",
                "INDEXED_DECLINE rhs_erased_illtyped_annotation [^\\r\\n]+",
                "INDEXED_DECLINE wrong_canonical_anchor [^\\r\\n]+",
                "PRIVATE_INDEXED_CONTROLS_DONE rhs positive_gate 3_declines exact_closed unchanged_axioms"
            ],
            "limit": 180,
            "options": {
                "COMPOSE_GROUP": "rhs"
            }
        },
        "hadd-static": {
            "source_file": "hadd_static_tests.ml",
            "markers": [
                "PRIVATE_BRIDGE_STATIC_DONE 11_assertions certified_false_is_decline unchanged_axioms"
            ],
            "limit": 180,
            "options": {}
        },
        "hadd-boundary": {
            "source_file": "hadd_boundary_tests.ml",
            "markers": [
                "HOL_MINDEX_BOUNDARY_TESTS_PASSED 4",
                "HOL_MUTUAL_BOUNDARY_TESTS_PASSED 4",
                "PRIVATE_BOUNDARY_DONE prefixes28_10_and27_9 totals29_11 trace3 unchanged_axioms"
            ],
            "limit": 180,
            "options": {}
        },
        "hadd-mixed": {
            "source_file": "hadd_mixed_tests.ml",
            "markers": [
                "PRIVATE_MIXED_DECODED exact_original_blocks count=6",
                "PRIVATE_MIXED_DONE exact_original_raw_poly_history three_invariants tamper_proof_failure rules29_11 unchanged_axioms"
            ],
            "limit": 180,
            "options": {}
        }
    })
    for group, count in [('type', 22), ('prop', 18), ('higher', 17), ('dependent', 15),
                         ('metadata_a', 17), ('metadata_b', 17), ('metadata_c', 17),
                         ('indices_a', 18), ('indices_b', 19), ('uniform_levels', 16),
                         ('uniform_params', 17), ('mixed', 16)]:
        result['indexed-' + group] = {
            'source': 'needs "hol/private_boot.ml";;\nneeds "hol/mindex_tests.ml";;\n'
                      f'l4_mindex_tests "{group}";;\n',
            'markers': [f'HOL_MINDEX_{group.upper()}_TESTS_PASSED {count}'],
            'limit': 180, 'options': {}}
    result['indexed-boundary'] = {
        'source': 'needs "hol/private_boot.ml";;\nneeds "hol/mindex_boundary_tests.ml";;\n'
                  'needs "hol/mutual_boundary_tests.ml";;\n',
        'markers': ['HOL_MINDEX_BOUNDARY_TESTS_PASSED 4', 'HOL_MUTUAL_BOUNDARY_TESTS_PASSED 4'],
        'limit': 180, 'options': {}}
    for group, count in [('rs', 25), ('mamb', 24), ('forged_index', 28),
                         ('forged_motive', 28), ('joint', 25), ('joint_forged', 6)]:
        result['indexed-history-' + group] = {
            'source_file': 'indexed_history.ml',
            'markers': [f'HOL_COMPOSE_HISTORY_{group.upper()}_PASSED {count}'],
            'limit': 180, 'options': {'HOL_HISTORY_GROUP': group}}
    for group in ('119', '120'):
        result['raw-function-file-' + group] = {
            'source_file': 'indexed_file_tests.ml',
            'markers': [f'PRIVATE_INDEXED_FILE_DONE {group} exact_original_history three_invariants tamper_decline unchanged_axioms'],
            'limit': 180, 'options': {'COMPOSE_GROUP': group}}
    typed = {
        'domain': ['hidden_domain_has_closed_formation_and_entry_bridge',
                   'nonuniform_beta_has_closed_formation_and_entry_bridge'],
        'telescope': ['second_domain_has_closed_formation_and_entry_bridge',
                      'nested_nonuniform_has_closed_formation_and_entry_bridge'],
        'result': ['result_beta_has_closed_formation_and_signature_conversion']}
    for group, declines in [('positive', 0), ('domain-positive', 1), ('domain', 3),
                            ('telescope', 2), ('formation', 3), ('metadata', 3),
                            ('rhs', 3), ('result', 2)]:
        result['raw-function-' + group] = {
            'source_file': 'indexed_control_tests.ml',
            'markers': [f'PRIVATE_INDEXED_CONTROLS_DONE {group} positive_gate {declines}_declines exact_closed unchanged_axioms',
                        'INDEXED_POSITIVE authentic119_control exact_closed'] +
                       ['INDEXED_TYPED_CONTROL ' + s for s in typed.get(group, [])],
            'limit': 180, 'options': {'COMPOSE_GROUP': group}}
    for group in ('positive', 'higher', 'dependent', 'prop', 'metadata', 'metadata2', 'negative'):
        result['mutual-' + group] = {
            'source': 'needs "hol/private_boot.ml";;\nneeds "hol/mutual_tests.ml";;\n'
                      f'l4_mutual_tests "{group}";;\nneeds "hol/mutual_boundary_tests.ml";;\n',
            'markers': [marker('MUTUAL_' + group.upper()), marker('MUTUAL_BOUNDARY')],
            'limit': 180, 'options': {}}
    for group in ('pred-general', 'pred-cases', 'sub-general', 'sub-cases',
                  'mul-general', 'mul-cases', 'pow-general'):
        result[group] = {
            'source_file': group.replace('-', '_') + '_tests.ml',
            'markers': [r'COMPOSED_WORK_PASS ' + group + r' [0-9]+'],
            'limit': 180, 'options': {}}
    for group in ('empty', 'contexts', 'wrappers'):
        result['pow-' + group] = {
            'source': 'needs "pow_cases_tests.ml";;\n'
                      f'run_pow_cases "{group}";;\n',
            'markers': [r'COMPOSED_WORK_PASS pow-' + group + r' [0-9]+'],
            'limit': 180, 'options': {}}
    raw = [
        ('bridge-static', 'bridge_static_tests.ml', 'BRIDGE_STATIC', {}),
        ('add-context-general', 'add_context_general_tests.ml', 'NAT_EVALUATION', {}),
        ('add-context', 'add_context_tests.ml', 'NAT_EVALUATION', {}),
        ('derived-add', 'derived_add_tests.ml', 'NAT_EVALUATION', {}),
        ('derived-add-wrappers', 'derived_add_wrapper_tests.ml', 'NAT_EVALUATION', {}),
        ('add-evaluation-general', 'add_evaluation_general_tests.ml', 'NAT_EVALUATION', {}),
        ('add-evaluation', 'add_evaluation_tests.ml', 'NAT_EVALUATION', {}),
        ('nat-recurrence-general', 'nat_recurrence_general_tests.ml', 'NAT_EVALUATION', {}),
        ('nat-recurrence', 'nat_recurrence_tests.ml', 'NAT_EVALUATION', {}),
        ('closed-syntax', 'closed_syntax_tests.ml', 'CLOSED_SYNTAX_CASES', {}),
        ('instantiation', 'instantiation_tests.ml', 'INSTANTIATION_CASES', {}),
        ('history-inventory', 'history_inventory_tests.ml', 'HISTORY_INVENTORY', {}),
        ('trace-empty', 'compose_mutual_trace_v2_tests.ml', 'MUTUAL_TRACE', {'COMPOSE_GROUP': 'empty'}),
        ('trace-recursive', 'compose_mutual_trace_v2_tests.ml', 'MUTUAL_TRACE', {'COMPOSE_GROUP': 'recursive'}),
        ('trace-forged', 'compose_mutual_trace_v2_tests.ml', 'MUTUAL_TRACE', {'COMPOSE_GROUP': 'forged'}),
        ('raw-positive', 'hol/raw_positive_tests.ml', 'RAW_POSITIVE', {}),
        ('raw-controls', 'hol/raw_control_tests.ml', 'RAW_CONTROLS', {}),
        ('raw-counterexample', 'hol/raw_counterexample_tests.ml', 'COUNTEREXAMPLE', {}),
        ('raw-e2e', 'hol/raw_e2e_tests.ml', 'RAW_FILES', {}),
        ('raw-head', 'hol/raw_head_positive_tests.ml', 'RAW_HEAD_POSITIVE', {}),
        ('raw-string-positive', 'hol/raw_string_positive_tests.ml', 'RAW_STRING_POSITIVE', {}),
        ('raw-string-native', 'hol/raw_string_native_tests.ml', 'RAW_STRING_NATIVE', {}),
        ('iterative-validation', 'compose_validation_tests.ml', 'COMPOSE_VALIDATION', {}),
    ]
    for group in ('a', 'b', 'c'):
        raw.append(('raw-string-' + group, 'hol/raw_string_negative_tests.ml',
                    'RAW_STRING_CONTROLS', {'RAW_STRING_GROUP': group}))
    for group in ('admission-gate', 'compute-one', 'wrong-result'):
        raw.append(('shift-' + group, 'compose_shift_tests.ml', 'COMPOSE_SHIFT_CASE',
                    {'COMPOSE_GROUP': group}))
    for group in ('quotient', 'structure', 'reflexive'):
        raw.append((group + '-files', 'compose_file_tests.ml', 'COMPOSE_FILES', {'COMPOSE_GROUP': group}))
    for tag, source, done, options in raw:
        result[tag] = {'source_file': source, 'markers': [r'PRIVATE_' + done + r'_DONE [^\r\n]+'],
                       'limit': 180, 'options': options}
    exact = {
        'bridge-static': 'PRIVATE_BRIDGE_STATIC_DONE 11_assertions certified_false_is_decline unchanged_axioms',
        'closed-syntax': 'PRIVATE_CLOSED_SYNTAX_CASES_DONE 550_assertions twelve_closed_terms unchanged_axioms',
        'instantiation': 'PRIVATE_INSTANTIATION_CASES_DONE 64_assertions seven_cases unchanged_rules unchanged_axioms',
        'history-inventory': 'PRIVATE_HISTORY_INVENTORY_DONE seven_controls three_general_lemmas unchanged_axioms',
        'trace-forged': 'PRIVATE_MUTUAL_TRACE_DONE forged decline no_certificate unchanged_axioms',
        'raw-positive': 'PRIVATE_RAW_POSITIVE_DONE exact_raw055 closed policy unique unchanged_axioms',
        'raw-counterexample': 'PRIVATE_COUNTEREXAMPLE_DONE old_bridge_accepts new_admission_declines exact_closed unchanged_axioms',
        'raw-e2e': 'PRIVATE_RAW_FILES_DONE authentic055_119_120_accept three_declines unchanged_axioms',
        'iterative-validation': 'PRIVATE_COMPOSE_VALIDATION_DONE iterative_syntax rules29_11 unchanged_axioms'}
    for group in ('empty', 'recursive'):
        exact['trace-' + group] = f'PRIVATE_MUTUAL_TRACE_DONE {group} exact_history invariants tamper_proof_failure unchanged_axioms'
    for tag, expected in exact.items():
        result[tag]['markers'] = [expected]
    result['preserved-full'] = {
        'source': 'needs "hol/private_boot.ml";;\nneeds "hol/raw_ctor_admission.ml";;\n' +
                  '\n'.join(f'needs "hol/{p}.ml";;' for p in FULL_FILES) + '\n' +
                  'if axioms()<>private_axioms then failwith "axiom change";;\n' +
                  'if private_native_rule_count<>29 || private_admission_rule_count<>11 '
                  'then failwith "rule count change";;\n' +
                  'print_endline "HOL_COMPOSITION_INVARIANTS_TESTS_PASSED 3";;\n',
        'markers': [marker(m) for m in FULL_MARKERS + ['COMPOSITION_INVARIANTS']], 'limit': 900,
        'options': {'HOL_PRIMITIVE_SUITE': 'pow', 'HOL_PRIMITIVE_POW_PHASE': 'factory'}}
    additional = early_variants.jobs()
    if result.keys() & additional.keys():
        raise ValueError('Duplicate early job registration')
    result.update(additional)
    return result


def inspect_log(text, expected):
    errors = ERROR.findall(text)
    found = {pattern: re.findall(r'(?m)^(?:#\s*)?(' + pattern + r')[ \t]*$', text)
             for pattern in expected}
    return errors, found, not errors and all(len(v) == 1 for v in found.values())


def verify_fixtures(suite):
    suite = suite.resolve()
    manifest = json.loads((suite / 'fixture-pins.json').read_text())
    expected = {}
    for entry in manifest['entries']:
        relative = Path(entry['path'])
        if (not relative.parts or relative.is_absolute() or '..' in relative.parts or
                relative.parts[0] != 'data' or str(relative) in expected):
            raise ValueError('Invalid fixture manifest path')
        path = suite / relative
        if any((suite / p).is_symlink() for p in [relative, *relative.parents]):
            raise ValueError('Symlinked fixture path')
        if digest(path) != entry['sha256'] or path.stat().st_size != entry['bytes']:
            raise ValueError('Fixture hash/size mismatch: ' + str(relative))
        expected[str(relative)] = entry['sha256']
    actual = {'data/' + p for p in inventory(suite / 'data')}
    if actual != set(expected):
        raise ValueError('Fixture inventory mismatch')
    return expected


def prepare_snapshot(destination):
    manifest_hash = digest(SUITE / 'fixture-pins.json')
    fixture_hashes = verify_fixtures(SUITE)
    origins = {}

    def copy_file(source, relative, expected_hash=None):
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        before = digest(source)
        if expected_hash is not None and before != expected_hash:
            raise RuntimeError('Pinned fixture changed before copying: ' + str(source))
        shutil.copyfile(source, target)
        if digest(source) != before or digest(target) != before:
            raise RuntimeError('Source changed while copying: ' + str(source))
        origins[str(source.relative_to(ROOT))] = before

    for directory in ('hol', 'frontend'):
        for p in sorted((ROOT / directory).glob('*.ml')):
            copy_file(p, p.relative_to(ROOT))
    for name in ('toolchain-env.sh', 'toolchain-exec.sh'):
        copy_file(ROOT / 'scripts' / name, 'scripts/' + name)
    for name in ('wire', 'replay', 'hol_input'):
        for ext in ('cmo', 'cmi'):
            p = ROOT / 'build/frontend' / (name + '.' + ext)
            copy_file(p, p.relative_to(ROOT))
    for subtree in ('data', 'drivers'):
        for p in sorted((SUITE / subtree).rglob('*')):
            if p.is_file():
                expected = fixture_hashes.get(str(p.relative_to(SUITE))) if subtree == 'data' else None
                if subtree == 'data' and expected is None:
                    raise RuntimeError('Unpinned fixture added during acquisition')
                copy_file(p, p.relative_to(SUITE / subtree), expected)
    copy_file(SUITE / 'native.sh', 'scripts/private-hol.sh')
    copy_file(SUITE / 'fixture-pins.json', 'tests/hol_composition/fixture-pins.json', manifest_hash)
    copy_file(SUITE / 'reference_environment_rules.ml', 'tests/hol_composition/reference_environment_rules.ml')
    copy_file(SUITE / 'reference_indexed_environment_rules.ml', 'tests/hol_composition/reference_indexed_environment_rules.ml')
    copy_file(Path(__file__).resolve(), 'tests/hol_composition/run.py')
    for name in ('early_variants.py', 'early_observers.py', 'early-pins.json'):
        copy_file(SUITE / name, 'tests/hol_composition/' + name)
    changed = [p for p, h in origins.items() if digest(ROOT / p) != h]
    if changed:
        raise RuntimeError('Source changed during snapshot acquisition: ' + repr(changed))
    (destination / 'toolchain').symlink_to((ROOT / 'toolchain').resolve(), target_is_directory=True)
    return origins


def cleanup_owned_process(process, allow_group=True):
    """Sole reaper only: the owned unreaped session leader reserves its PID/PGID."""
    errors = []
    actions = []
    unreaped = False
    try:
        unreaped = process.poll() is None
    except Exception as error:
        errors.append('poll: ' + repr(error))
    group_signalled = False
    if unreaped and allow_group:
        # No wait/poll or concurrent reaper may intervene before this signal.
        try:
            os.killpg(process.pid, signal.SIGKILL)
            group_signalled = True
            actions.append('owned_unreaped_group_kill')
        except ProcessLookupError:
            actions.append('owned_group_already_absent')
        except Exception as error:
            errors.append('killpg: ' + repr(error))
    if process.returncode is None:
        if not group_signalled:
            try:
                process.kill()
                actions.append('direct_handle_kill')
            except ProcessLookupError:
                actions.append('direct_handle_already_absent')
            except Exception as error:
                errors.append('kill: ' + repr(error))
        try:
            process.wait(timeout=10)
        except Exception as error:
            errors.append('wait: ' + repr(error))
    if process.stdin is not None and not process.stdin.closed:
        try:
            process.stdin.close()
        except Exception as error:
            errors.append('stdin.close: ' + repr(error))
    presence = {}
    for name, probe in (('pid_absent', os.kill), ('process_group_absent', os.killpg)):
        try:
            probe(process.pid, 0)
            presence[name] = False
        except ProcessLookupError:
            presence[name] = True
        except Exception as error:
            presence[name] = None
            errors.append(name + ': ' + repr(error))
    reaped = process.returncode is not None
    return dict(presence, pid=process.pid, reaped=reaped, actions=actions, errors=errors,
                verified=reaped and all(v is True for v in presence.values()) and not errors)


def _run_job(snapshot, report_dir, tag, job, publish=True):
    source = job.get('source')
    if source is None:
        source = (snapshot / job['source_file']).read_text()
    source += '\nexit 0;;\n'
    before = inventory(snapshot)
    start = time.monotonic()
    timed_out = False
    primary_error = None
    log_path = report_dir / (tag + '.log')
    with log_path.open('xb') as log:
        process = subprocess.Popen(['sh', 'scripts/private-hol.sh'], cwd=snapshot,
                                   env=dict(os.environ, LINE_EDITOR='env', **job['options']),
                                   stdin=subprocess.PIPE, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            process.communicate(source.encode(), timeout=job['limit'])
        except subprocess.TimeoutExpired:
            timed_out = True
        except BaseException as error:
            primary_error = error
        finally:
            cleanup = cleanup_owned_process(process)
    errors, found, log_passed = inspect_log(log_path.read_text(errors='replace'), job['markers'])
    after = inventory(snapshot)
    result = {'tag': tag, 'passed': log_passed and not timed_out and process.returncode == 0
              and before == after and cleanup['verified'] and primary_error is None,
              'returncode': process.returncode,
              'timed_out': timed_out, 'limit_seconds': job['limit'],
              'seconds': round(time.monotonic() - start, 3), 'pid': process.pid,
              'reaped': cleanup['reaped'], 'process_group_absent': cleanup['process_group_absent'],
              'cleanup': cleanup, 'primary_error': repr(primary_error) if primary_error is not None else None,
              'errors': errors,
              'markers': found, 'options': job['options'], 'before': before, 'after': after,
              'input_sha256': hashlib.sha256(source.encode()).hexdigest(),
              'log_sha256': digest(log_path)}
    (report_dir / (tag + '.input.ml')).write_text(source)
    if publish or primary_error is not None:
        (report_dir / (tag + '.json')).write_text(json.dumps(result, indent=2) + '\n')
    if publish:
        print(json.dumps({k: v for k, v in result.items() if k not in ('before', 'after')}), flush=True)
    if primary_error is not None:
        (report_dir / (tag + '.execution-error.json')).write_text(json.dumps(result, indent=2) + '\n')
        primary_error.add_note('Owned-process cleanup: ' + json.dumps(cleanup, sort_keys=True))
        raise primary_error
    return result


def run_job(snapshot, report_dir, tag, job, frozen_snapshot=None):
    if not tag.startswith('early-') and 'early_variant' not in job:
        return _run_job(snapshot, report_dir, tag, job)
    if not re.fullmatch(r'early-[a-z-]+', tag):
        raise ValueError('Invalid early job tag')
    context = None
    result = None
    stage = 'preparation'
    try:
        context = early_variants.prepare(snapshot, report_dir, tag, job, frozen_snapshot)
        source = job['source'] + 'exit 0;;\n'
        expected_input = report_dir / (tag + '.prepared-input.ml')
        with expected_input.open('x') as stream:
            stream.write(source)
        input_pin = digest(expected_input)
        if input_pin != context['entry']['input_sha256']:
            raise ValueError('Early input differs from tested driver invocation')
        stage = 'prelaunch'
        early_variants.check_ready(context)
        native_job = dict(job, source=job['source'][:-1])
        stage = 'execution'
        result = _run_job(context['derived'], report_dir, tag, native_job, publish=False)
        result['launched'] = True
        stage = 'postflight'
        post = early_variants.postflight(context)
        input_held = (not expected_input.is_symlink() and digest(expected_input) == input_pin
                      and result['input_sha256'] == input_pin)
        copied_pins_held = (result['before'] == context['derived_pins']['files'] and
                           result['after'] == context['derived_pins']['files'])
        result.update(stage='complete', early_postflight=post,
                      prepared_input_unchanged=input_held)
        result['passed'] = result['passed'] and post['passed'] and input_held and copied_pins_held
    except Exception as error:
        if result is None:
            result = {'tag': tag,
                  'launched': False if stage in ('preparation', 'prelaunch') else None,
                  'returncode': None, 'timed_out': False, 'reaped': None,
                  'process_group_absent': None, 'limit_seconds': job.get('limit')}
        result.update(passed=False, stage=stage, error=type(error).__name__ + ': ' + str(error))
        if context is not None:
            result['early_postflight'] = early_variants.postflight(context)
    if context is not None:
        result['early'] = {k: context['provenance'][k] for k in (
            'variant', 'category', 'observer_function', 'expected_assertions',
            'production_core_sha256', 'unmodified_test_core_sha256', 'loaded_test_core_sha256')}
        result['provenance_sha256'] = context['provenance_sha256']
    (report_dir / (tag + '.json')).write_text(json.dumps(result, indent=2) + '\n')
    visible = {k: v for k, v in result.items() if k not in ('before', 'after')}
    if 'early_postflight' in visible:
        visible['early_postflight'] = {k: v for k, v in visible['early_postflight'].items()
                                       if not k.endswith('_pins')}
    print(json.dumps(visible), flush=True)
    return result


def result_summary(result):
    summary = {k: result[k] for k in ('tag', 'passed')}
    if 'early' in result:
        summary.update({k: result['early'][k] for k in ('category', 'expected_assertions')})
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('groups', nargs='*', help='Exact groups; default is every group')
    parser.add_argument('--list', action='store_true', help='List groups without starting HOL')
    args = parser.parse_args()
    available = jobs()
    if args.list:
        print('\n'.join(available))
        return 0
    selected = args.groups or list(available)
    if len(set(selected)) != len(selected) or set(selected) - available.keys():
        parser.error('Unknown or repeated group')
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    report = ROOT / 'build/reports' / f'hol-composition-{stamp}-{os.getpid()}'
    report.mkdir(parents=True)
    snapshot = report / 'snapshot'
    snapshot.mkdir()
    origins = prepare_snapshot(snapshot)
    frozen_snapshot = early_variants.tree_pins(snapshot)
    (report / 'provenance.json').write_text(json.dumps({
        'origin_root': str(ROOT), 'origin_sha256': origins,
        'snapshot_sha256': inventory(snapshot), 'selected': selected,
        'snapshot_symlinks': frozen_snapshot['symlinks'],
        'unselected': [g for g in available if g not in selected],
        'toolchain': str((ROOT / 'toolchain').resolve()),
        'boundary': 'Project sources, bytecode and fixture snapshot; toolchain/OS not hermetic.'
    }, indent=2) + '\n')
    print('REPORT ' + str(report), flush=True)
    results = []
    for tag in selected:
        results.append(run_job(snapshot, report, tag, available[tag], frozen_snapshot))
        (report / 'summary.json').write_text(json.dumps({
            'selected': selected, 'results': [result_summary(r) for r in results],
            'unexecuted': selected[len(results):],
            'complete': len(results) == len(selected),
            'passed': len(results) == len(selected) and all(r['passed'] for r in results)
        }, indent=2) + '\n')
        if not results[-1]['passed']:
            return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
