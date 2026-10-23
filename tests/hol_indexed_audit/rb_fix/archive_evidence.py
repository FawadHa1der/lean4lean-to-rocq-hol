#!/usr/bin/env python3
"""Archive bounded RBTree diagnostic/regression evidence after private-server cleanup."""

import argparse
import difflib
import json
import os
from pathlib import Path
import re

import run as suite


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('private_parent', type=Path)
    args = parser.parse_args()
    base = args.private_parent.resolve(strict=True)
    suite.plan(base / 'rb-fixed')
    provenance = (base / 'rb-fixed-runtime.json').read_bytes()
    _, runtime = suite.runtime(base / 'rb-fixed', base / 'rb-fixed-runtime.json', suite.p2.sha(provenance))
    records, files = {}, {}
    phases = [('rb-probe', 'rb-probe', 'rb_probe_driver.py'),
              ('rb-probe2', 'rb-probe2', 'rb_probe2_driver.py'),
              ('rb-native', 'rb-fixed', 'rb_native_driver.py')]
    for phase, tree, driver in phases:
        log = (base / (phase + '.log')).read_bytes()
        raw = (base / (phase + '.json')).read_bytes()
        status = json.loads(raw)
        if len(log) > 2 * 1024 * 1024 or status['log_bytes'] != len(log) or status['log_sha256'] != suite.p2.sha(log):
            raise ValueError('bounded transcript integrity failure')
        if status['exit_code'] != 0 or not status['unchanged'] or status['project_snapshot_before'] != status['project_snapshot_after']:
            raise ValueError('private run did not finish with stable project provenance')
        for name, digest in status['inputs'].items():
            suite.p2.pinned(base / tree / name, digest)
        text = log.decode(errors='replace')
        if re.search(r'(?:^|\n|# )\s*(?:Error:|Exception:|Parse error|Error in included file)', text):
            raise ValueError('HOL load error in transcript')
        if phase == 'rb-native':
            checks = [int(n) for n in re.findall(r'^indexed check (\d+):', text, re.MULTILINE)]
            if checks != list(range(1, 88)) or 'HOL_INDEXED_TESTS_PASSED 87' not in text or 'P2_NATIVE_COMPLETE' not in text:
                raise ValueError('native regression assertions incomplete')
        else:
            checks = []
            if 'RB_PROBE_COMPLETE' not in text or text.count('RB_UNSOLVED ') != 2:
                raise ValueError('RBTree diagnostic incomplete')
        if phase == 'rb-probe2':
            for marker in ('RB_CONVERSION_EARLY l4_vars (SUC 0) 3',
                           'RB_CONVERSION_REVERTED l4_vars 1 3',
                           'RB_CONVERSION_FIXED [L4BVar 3]',
                           'RB_CONVERSION_CLOSED_EXACT_NO_AXIOMS'):
                if marker not in text:
                    raise ValueError('converter mechanism/certificate probe incomplete')
            if text.count('RB_UNSOLVED indexed.field.3.premise.1') != 2:
                raise ValueError('field obligation was not localized for both cases')
            files['conversion_probe.ml'] = suite.p2.pinned(base / tree / 'conversion_probe.ml', status['conversion_probe_sha256'])
        records[phase] = {'exit_code': status['exit_code'], 'seconds': status['seconds'],
                          'log_sha256': status['log_sha256'], 'log_bytes': len(log),
                          'native_assertions': len(checks), 'project_provenance_unchanged': True,
                          'provenance_sha256': suite.p2.sha(raw)}
        files.update({phase + '.log': log, phase + '.json': raw, driver: (base / driver).read_bytes()})
    processes = {}
    for key in ('supervisor_pid', 'hol_pid'):
        pid = runtime['startup'][key]
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            processes[key] = {'pid': pid, 'exists': False}
        else:
            raise ValueError('private server process still exists')
    if Path(runtime['startup']['socket']).exists():
        raise ValueError('private socket still exists')
    original = (base / 'fixed/hol/environment.ml').read_text()
    if suite.p2.sha(original.encode()) != suite.p2.FIXED_ENV_SHA:
        raise ValueError('pre-converter baseline changed')
    for tree in ('rb-probe', 'rb-probe2'):
        changed = (base / tree / 'hol/environment.ml').read_text()
        files[tree + '.patch'] = ''.join(difflib.unified_diff(original.splitlines(True), changed.splitlines(True),
                                                             fromfile='a/hol/environment.ml', tofile='b/hol/environment.ml')).encode()
    records.update(cleanup={'processes': processes, 'socket_removed': True},
                   base_environment_sha256=suite.p2.FIXED_ENV_SHA,
                   fixed_environment_sha256=suite.ENV_SHA,
                   runtime_provenance_sha256=suite.p2.sha(provenance))
    files['summary.json'] = (json.dumps(records, indent=2, sort_keys=True) + '\n').encode()
    destination = suite.HERE / 'evidence'
    destination.mkdir()
    for name, data in files.items():
        with (destination / name).open('xb') as stream:
            stream.write(data)
    print(json.dumps(records, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
