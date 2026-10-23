#!/usr/bin/env python3
"""Run only the five additive capability groups, with bounded real HOL stages."""
import argparse
import codecs
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import signal
import subprocess
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
TESTS = ROOT / 'tests/hol_reflection'
GROUPS = ('bool', 'ite', 'dite', 'nat-eq', 'nat-le')
ERRORS = re.compile(r'(^|\s)(Error:|Exception:)|Parse error|Error in included file|'
                    r'^(NAT|COMPOSED|UNIFIED)_WORK_FAIL ', re.M)
MARKERS = re.compile(r'^(?:REFLECTION_LIBRARY_READY|COMPOSED_SETUP_READY|'
                     r'NAT_INSTANTIATION_SETUP_READY|UNIFIED_SETUP_READY|'
                     r'(?:NAT|COMPOSED|UNIFIED)_WORK_PASS)(?:\s|$)')
MAX_LOG = 16 * 1024 * 1024


class RunnerFailure(Exception):
    pass


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(root=ROOT):
    tests = root / 'tests/hol_reflection'
    paths = sorted((root / 'hol').glob('*.ml')) + sorted(tests.glob('*.ml'))
    paths += [tests / 'SOURCE_PINS.json', root / 'scripts/test-hol-reflection.py',
              root / 'scripts/toolchain-exec.sh', root / 'scripts/toolchain-env.sh']
    return {str(p.relative_to(root)): sha(p) for p in paths}


def production_closure():
    visited = set()
    def walk(rel):
        if rel in visited:
            return
        visited.add(rel)
        path = ROOT / rel
        if not path.exists():
            raise RuntimeError('missing library dependency: ' + rel)
        if rel.startswith('tests/') or '_fixtures.ml' in rel:
            raise RuntimeError('test dependency in production entry point: ' + rel)
        for dependency in re.findall(r'^needs "([^"]+)";;', path.read_text(), re.M):
            if dependency.startswith(('hol/', 'tests/')):
                walk(dependency)
    walk('hol/reflection.ml')
    return sorted(visited)


def plan(groups):
    if groups[0].startswith('nat-'):
        if len(groups) != 1:
            raise ValueError('each Nat group uses a separate freshly admitted environment')
        eq = groups[0] == 'nat-eq'
        prefix = 'eq' if eq else 'le'
        dependencies = ('beq beq-diag eq-true eq-false dec-eq' if eq else
            'ble ble-diag nat-le le-class le-projection le-instance zero-le succ-le '
            'le-true ble-step ble-of-le le-false dec-le').split()
        ordinary = ('dec-infer gadget-infer 1').split()
        derived = ('seed close-1 close-2 close-3 close-4 arg-1 arg-2 arg-3 arg-4 '
                   'wrapper-init wrapper-1 wrapper-2 wrapper-3 proof-link delta finish').split()
        stages = [(x, 'Lean4hol_nat_tests', 'NAT', 'preparation') for x in dependencies]
        stages += [(prefix + '-' + x, 'Lean4hol_nat_tests', 'NAT', 'preparation') for x in ordinary]
        stages += [(prefix + '-' + x, 'Lean4hol_nat_composition_tests', 'NAT', 'preparation')
                   for x in derived]
        stages += [(prefix + '-positive', 'Lean4hol_nat_tests', 'NAT', 'capability'),
                   (prefix + '-negatives', 'Lean4hol_nat_tests', 'NAT', 'negative'),
                   (prefix + '-proof-negatives', 'Lean4hol_nat_tests', 'NAT', 'negative'),
                   (prefix + '-inst-negatives', 'Lean4hol_nat_composition_tests', 'NAT', 'negative')]
        return 'nat_instantiation_tests.ml', 'NAT_INSTANTIATION_SETUP_READY', stages
    if any(x.startswith('nat-') for x in groups):
        raise ValueError('do not mix Nat and Boolean/Reflection environments')
    phases = ['bool'] if 'bool' in groups else []
    phases += ['ite-types']
    if 'ite' in groups:
        phases += ['ite-true-proof', 'ite-false-proof', 'one-ite']
    if 'dite' in groups:
        phases += ['dite-types', 'dite-true-proof', 'dite-false-proof', 'one-dite']
    phases += ['negatives', 'proof-negatives']
    stages = [(x, 'Lean4hol_composed_tests', 'COMPOSED',
               'capability' if x in ('bool', 'one-ite', 'one-dite') else
               'negative' if 'negatives' in x else 'preparation') for x in phases]
    return 'composed_tests.ml', 'COMPOSED_SETUP_READY', stages


def fixture_stages(fixture, ready):
    return [dict(stage='setup-fixtures', kind='setup',
        command=f'needs "tests/hol_reflection/{fixture}";;', marker=ready + r'\s*')]


def freeze_sources(root, destination, before):
    """No source code is evaluated to copy or discover dependencies."""
    destination.mkdir()
    for rel, digest in before.items():
        name = Path(rel)
        if name.is_absolute() or '..' in name.parts or (root / rel).is_symlink():
            raise RunnerFailure('nonlocal/symlink source: ' + rel)
        data = (root / rel).read_bytes()
        if hashlib.sha256(data).hexdigest() != digest:
            raise RunnerFailure('source changed while copying: ' + rel)
        target = destination / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream:
            stream.write(data)
        if sha(target) != digest:
            raise RunnerFailure('copy integrity mismatch: ' + rel)
        target.chmod(0o444)
    if inventory(root) != before or inventory(destination) != before:
        raise RunnerFailure('source inventory changed during snapshot')
    toolchain = (root / 'toolchain').resolve(strict=True)
    (destination / 'toolchain').symlink_to(toolchain, target_is_directory=True)
    for directory in sorted((p for p in destination.rglob('*') if p.is_dir() and not p.is_symlink()),
                            key=lambda p: len(p.parts), reverse=True):
        directory.chmod(0o555)
    destination.chmod(0o555)
    return {'symlink': str(destination / 'toolchain'), 'target': str(toolchain),
            'scope': 'External shared toolchain; binaries, libraries and runtime are not attested.'}


def group_exists(pgid):
    try:
        os.killpg(pgid, 0)
        return True
    except ProcessLookupError:
        return False


def cleanup_group(process, cap=5.0):
    """Single-reaper cleanup: never signal a numeric group after its leader is reaped."""
    if process.pid == os.getpgrp():
        raise RunnerFailure('refusing cleanup of runner process group')
    errors = []
    observations = []
    deadline = time.monotonic() + cap
    for sig, grace in ((signal.SIGTERM, 0.25), (signal.SIGKILL, cap)):
        try:
            if process.poll() is not None:
                break
        except OSError as error:
            observations.append('ownership poll: ' + repr(error))
            break
        # No other thread may reap this Popen. Until we poll/wait again, even
        # an exited leader reserves its PID and thus this process-group ID.
        try:
            os.killpg(process.pid, sig)
        except ProcessLookupError:
            break
        except OSError as error:
            observations.append('killpg: ' + repr(error))
        until = min(deadline, time.monotonic() + grace)
        while time.monotonic() < until:
            try:
                if process.poll() is not None:
                    break
                if not group_exists(process.pid):
                    break
            except OSError as error:
                observations.append('group probe: ' + repr(error))
                break
            time.sleep(0.02)
        try:
            if process.returncode is not None or not group_exists(process.pid):
                break
        except OSError:
            pass
    try:
        process.wait(timeout=max(0.01, deadline - time.monotonic()))
    except (OSError, subprocess.TimeoutExpired) as error:
        errors.append('wait: ' + repr(error))
    try:
        absent = not group_exists(process.pid)
    except OSError as error:
        absent = False
        errors.append('final group probe: ' + repr(error))
    # A transient probe/signalling failure is resolved only by final absence
    # and a reaped parent, never by interpreting EPERM as an absent group.
    if not absent or process.returncode is None:
        errors.extend(observations)
    if not absent:
        errors.append('numeric process group remains; ownership after reaping is not established')
    return {'parent_reaped': process.returncode is not None, 'group_absent': absent,
            'cleanup_errors': errors, 'cleanup_observations': observations,
            'exit': process.returncode}


class Transcript:
    def __init__(self, pipe, stream, stages, nonce, limit):
        self.pipe, self.stream, self.stages, self.nonce, self.limit = pipe, stream, stages, nonce, limit
        self.selector = selectors.DefaultSelector()
        os.set_blocking(pipe.fileno(), False)
        self.selector.register(pipe, selectors.EVENT_READ)
        self.decoder = codecs.getincrementaldecoder('utf-8')(errors='replace')
        self.pending, self.errors, self.byte_count = '', [], 0
        self.active, self.eof = None, False
        self.counts, self.done = [0] * len(stages), [0] * len(stages)

    def fault(self, text):
        if len(self.errors) < 16:
            self.errors.append(text[:500])

    def line(self, line):
        if ERRORS.search(line):
            self.fault('HOL error: ' + line)
        if MARKERS.match(line):
            matches = [i for i, s in enumerate(self.stages) if re.fullmatch(s['marker'], line)]
            if len(matches) != 1:
                self.fault('unexpected/ambiguous stage marker: ' + line)
            else:
                i = matches[0]
                self.counts[i] += 1
                if i != self.active or self.counts[i] != 1 or self.done[i]:
                    self.fault('duplicate/out-of-order stage marker: ' + line)
        if line.startswith('REFLECTION_STAGE_DONE '):
            match = re.fullmatch(r'REFLECTION_STAGE_DONE ' + self.nonce + r' (\d+)', line)
            i = int(match.group(1)) if match else -1
            if i < 0 or i >= len(self.stages):
                self.fault('unexpected completion marker: ' + line)
            else:
                self.done[i] += 1
                if i != self.active or self.done[i] != 1 or self.counts[i] != 1:
                    self.fault('duplicate/out-of-order completion marker: ' + line)

    def poll(self, timeout=0):
        if self.eof:
            if timeout:
                time.sleep(min(timeout, 0.02))
            return
        for _, _ in self.selector.select(timeout):
            data = os.read(self.pipe.fileno(), 65536)
            if not data:
                self.eof = True
                self.selector.unregister(self.pipe)
            room = max(0, self.limit - self.byte_count)
            if len(data) > room:
                self.fault('log byte limit exceeded; capture is incomplete')
            kept = data[:room]
            self.stream.write(kept)
            self.byte_count += len(kept)
            self.pending += self.decoder.decode(kept, final=self.eof)
            lines = self.pending.split('\n')
            self.pending = lines.pop()
            for line in lines:
                self.line(line.rstrip('\r'))
            if self.eof and self.pending:
                self.line(self.pending)
                self.pending = ''

    def close(self):
        self.selector.close()
        self.pipe.close()


def final_log_check(path, stages, nonce):
    text = path.read_text(errors='replace')
    errors = []
    if ERRORS.search(text):
        errors.append('full final log contains HOL errors')
    for i, stage in enumerate(stages):
        if len(re.findall('^' + stage['marker'] + '$', text, re.M)) != 1:
            errors.append('final stage marker count is not one: ' + stage['stage'])
        if len(re.findall(r'^REFLECTION_STAGE_DONE ' + nonce + ' ' + str(i) + '$', text, re.M)) != 1:
            errors.append('final completion marker count is not one: ' + stage['stage'])
    known = [stage['marker'] for stage in stages]
    for line in text.splitlines():
        if MARKERS.match(line) and not any(re.fullmatch(pattern, line) for pattern in known):
            errors.append('unknown final stage marker')
        if line.startswith('REFLECTION_STAGE_DONE ') and not any(
                line == 'REFLECTION_STAGE_DONE ' + nonce + ' ' + str(i) for i in range(len(stages))):
            errors.append('unknown final completion marker')
    return errors[:32]


def run_session(command, cwd, directory, stages, stage_cap, *, log_limit=MAX_LOG, cleanup_cap=5.0):
    """Also used by synthetic process controls, which are NOT HOL verdict tests."""
    start = time.monotonic()
    nonce = uuid.uuid4().hex
    report = {'stages': [], 'pid': None, 'operational_errors': [], 'parent_reaped': False,
              'group_absent': False, 'cleanup_errors': [], 'passed': False, 'exit': None,
              'stage_cap_seconds': stage_cap, 'log_limit_bytes': log_limit, 'completion_nonce': nonce}
    process = transcript = None
    logpath = directory / 'hol.log'
    with logpath.open('xb') as log:
        try:
            process = subprocess.Popen(command, cwd=cwd, env=dict(os.environ, LINE_EDITOR='env', HOL_HELPER_TRACE='1'),
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
            report['pid'] = process.pid
            os.set_blocking(process.stdin.fileno(), False)
            transcript = Transcript(process.stdout, log, stages, nonce, log_limit)
            for i, stage in enumerate(stages):
                transcript.poll()
                if transcript.errors:
                    raise RunnerFailure('; '.join(transcript.errors))
                transcript.active = i
                began = time.monotonic()
                deadline = began + stage_cap
                command_bytes = (stage['command'] + '\nPrintf.printf "\\nREFLECTION_STAGE_DONE ' +
                                 nonce + ' ' + str(i) + '\\n%!";;\n').encode()
                while True:
                    if command_bytes:
                        try:
                            count = os.write(process.stdin.fileno(), command_bytes)
                            command_bytes = command_bytes[count:]
                        except BlockingIOError:
                            pass
                    transcript.poll(min(0.05, max(0, deadline - time.monotonic())))
                    ended = time.monotonic()
                    expired = ended >= deadline
                    completed = transcript.counts[i] == 1 and transcript.done[i] == 1 and not command_bytes
                    if completed or transcript.errors or expired or process.poll() is not None:
                        row = dict(stage=stage['stage'], kind=stage['kind'],
                            passed=completed and not transcript.errors and not expired,
                            timed_out=expired, errors_detected=bool(transcript.errors),
                            elapsed_seconds=ended-began, end_to_end_seconds=ended-start,
                            marker_count=transcript.counts[i], completion_count=transcript.done[i])
                        report['stages'].append(row)
                        print(json.dumps(row), flush=True)
                        if not row['passed']:
                            raise RunnerFailure('stage failed: ' + stage['stage'])
                        break
            process.stdin.close()
            deadline = time.monotonic() + cleanup_cap
            while process.poll() is None and time.monotonic() < deadline:
                transcript.poll(0.02)
            if process.poll() is None:
                raise RunnerFailure('parent failed to exit after EOF')
        except BaseException as error:
            report['operational_errors'].append(type(error).__name__ + ': ' + str(error)[:1000])
        finally:
            if process is not None:
                try:
                    if not process.stdin.closed:
                        process.stdin.close()
                except BaseException as error:
                    report['operational_errors'].append('stdin close: ' + repr(error))
                try:
                    report.update(cleanup_group(process, cleanup_cap))
                except BaseException as error:
                    report['cleanup_errors'].append('cleanup failure: ' + repr(error))
                    report['parent_reaped'] = process.returncode is not None
            if transcript is not None:
                try:
                    deadline = time.monotonic() + cleanup_cap
                    while not transcript.eof and time.monotonic() < deadline:
                        transcript.poll(0.02)
                    if not transcript.eof:
                        transcript.fault('stdout did not close after cleanup; possible escaped writer')
                except BaseException as error:
                    report['operational_errors'].append('final drain: ' + repr(error))
                finally:
                    report['stream_errors'] = transcript.errors
                    try:
                        transcript.close()
                    except BaseException as error:
                        report['operational_errors'].append('transcript close: ' + repr(error))
    report['total_seconds'] = time.monotonic() - start
    report['final_log_errors'] = final_log_check(logpath, stages, nonce)
    report['log_sha256'] = sha(logpath)
    report['passed'] = (report['exit'] == 0 and report['parent_reaped'] and report['group_absent']
        and not report['operational_errors'] and not report['cleanup_errors']
        and not report.get('stream_errors') and not report['final_log_errors']
        and len(report['stages']) == len(stages) and all(s['passed'] for s in report['stages']))
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('groups', nargs='*')
    parser.add_argument('--smoke', action='store_true', help='fixture-free library load only; no capability groups')
    parser.add_argument('--stage-cap', type=int, default=180)
    parser.add_argument('--evidence-dir', type=Path, default=ROOT / 'build/reflection-evidence')
    args = parser.parse_args()
    if (not 0 < args.stage_cap <= 180 or len(set(args.groups)) != len(args.groups)
            or any(g not in GROUPS for g in args.groups) or args.smoke == bool(args.groups)):
        parser.error('use --smoke OR unique capability groups; cap must be 1..180')
    stages = [dict(stage='setup-library', kind='setup',
        command='needs "tests/hol_reflection/library_smoke.ml";;',
        marker=r'REFLECTION_LIBRARY_READY native=29 admission=11\s*')]
    try:
        if not args.smoke:
            fixture, ready, planned = plan(args.groups)
            stages.extend(fixture_stages(fixture, ready))
            for phase, module, prefix, kind in planned:
                assert phase not in ('eq-3', 'le-3'), 'old whole conversion replay is forbidden'
                stages.append(dict(stage=phase, kind=kind, command=f'{module}.run "{phase}";;',
                                   marker=rf'{prefix}_WORK_PASS {re.escape(phase)} \d+\s*'))
    except ValueError as error:
        parser.error(str(error))
    directory = args.evidence_dir.resolve() / (time.strftime('%Y%m%dT%H%M%S') + '-' +
        ('smoke' if args.smoke else '-'.join(args.groups)) + '-' + uuid.uuid4().hex[:8])
    directory.mkdir(parents=True, mode=0o700)
    print(directory, flush=True)
    report = {'groups': args.groups, 'fixture_free_smoke': args.smoke, 'source_root': str(ROOT),
              'passed': False, 'operational_errors': []}
    snapshot = directory / 'source'
    previous_handler = signal.getsignal(signal.SIGTERM)
    def terminate(signum, frame):
        raise RunnerFailure('runner received SIGTERM')
    signal.signal(signal.SIGTERM, terminate)
    try:
        report['sources_before'] = inventory()
        report['production_closure'] = production_closure()
        pins = json.loads((TESTS / 'SOURCE_PINS.json').read_text())
        for rel, digest in pins['fixture_files'].items():
            if report['sources_before'].get(rel) != digest:
                raise RunnerFailure('typed fixture pin mismatch: ' + rel)
        report['toolchain'] = freeze_sources(ROOT, snapshot, report['sources_before'])
        report['execution_root'] = str(snapshot)
        report['expected_native_rules'], report['expected_admission_rules'] = 29, 11
        report.update(run_session(['sh', 'scripts/toolchain-exec.sh', 'hol.sh'], snapshot,
                                  directory, stages, args.stage_cap))
    except BaseException as error:
        report['operational_errors'].append(type(error).__name__ + ': ' + str(error)[:1000])
        report['passed'] = False
    finally:
        signal.signal(signal.SIGTERM, previous_handler)
        try:
            report['sources_after'] = inventory()
            report['snapshot_after'] = inventory(snapshot)
            report['source_integrity'] = (report.get('sources_before') == report['sources_after'] ==
                report['snapshot_after'] and (snapshot / 'toolchain').is_symlink() and
                str((snapshot / 'toolchain').resolve()) == report.get('toolchain', {}).get('target'))
        except BaseException as error:
            report['source_integrity'] = False
            report['operational_errors'].append('final inventory: ' + repr(error))
        report['passed'] = report['passed'] and report['source_integrity'] and not report['operational_errors']
        with (directory / 'report.json').open('x') as stream:
            stream.write(json.dumps(report, indent=2) + '\n')
        print(json.dumps({k:v for k,v in report.items() if k not in
            ('sources_before','sources_after','snapshot_after','production_closure')}, indent=2), flush=True)
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
