#!/usr/bin/env python3
"""Preserve bounded private-run evidence; never modify a production source."""

import argparse
import difflib
import json
import os
from pathlib import Path
import re

import run_targeted as target


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('private_parent', type=Path)
    args = parser.parse_args()
    base = args.private_parent.resolve(strict=True)
    target.plan(base / 'fixed')
    provenance = (base / 'fixed-runtime.json').read_bytes()
    runtime = json.loads(provenance)
    target.check_runtime(base / 'fixed', base / 'fixed-runtime.json', target.sha(provenance))
    records = {}
    for phase in ('probe', 'native'):
        data = (base / (phase + '.log')).read_bytes()
        info = json.loads((base / (phase + '.json')).read_bytes())
        if len(data) > 2 * 1024 * 1024 or info['log_bytes'] != len(data) or info['log_sha256'] != target.sha(data):
            raise ValueError('log integrity/size check failed')
        if info['exit_code'] != 0:
            raise ValueError('private HOL process did not exit cleanly')
        text = data.decode(errors='replace')
        if re.search(r'(?:^|\n|# )\s*(?:Error:|Exception:|Parse error|Error in included file)', text):
            raise ValueError('private HOL load error')
        if phase == 'native':
            checks = [int(n) for n in re.findall(r'^indexed check (\d+):', text, re.MULTILINE)]
            if checks != list(range(1, 88)) or 'HOL_INDEXED_TESTS_PASSED 87' not in text or 'P2_NATIVE_COMPLETE' not in text:
                raise ValueError('native indexed assertions are incomplete')
        else:
            if 'P2_PROBE_COMPLETE' not in text or text.count('P2_UNSOLVED_FLAG 7') != 2:
                raise ValueError('diagnostic obligation capture is incomplete')
            checks = []
        for name, digest in info['inputs'].items():
            target.pinned(base / ('probe' if phase == 'probe' else 'fixed') / name, digest)
        records[phase] = {'exit_code': info['exit_code'], 'seconds': info['seconds'],
                          'log_sha256': info['log_sha256'], 'log_bytes': len(data),
                          'native_assertions': len(checks)}
    processes = {}
    for key in ('supervisor_pid', 'hol_pid'):
        pid = runtime['startup'][key]
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            processes[key] = {'pid': pid, 'exists': False}
        else:
            raise ValueError('private server PID still exists: ' + str(pid))
    if Path(runtime['startup']['socket']).exists():
        raise ValueError('private socket still exists')
    records.update(cleanup={'processes': processes, 'socket_removed': True},
                   review_manifest_sha256=target.REVIEW_SHA,
                   fixed_environment_sha256=target.FIXED_ENV_SHA,
                   runtime_provenance_sha256=target.sha(provenance))
    destination = target.HERE / 'evidence'
    destination.mkdir()
    names = ['probe.log', 'probe.json', 'probe_driver.py', 'native.log', 'native.json', 'native_driver.py']
    for name in names:
        with (destination / name).open('xb') as stream:
            stream.write((base / name).read_bytes())
    original = (target.AUDIT / 'snapshot/hol/environment.ml').read_text()
    instrumented = (base / 'probe/hol/environment.ml').read_text()
    trace_patch = ''.join(difflib.unified_diff(original.splitlines(True), instrumented.splitlines(True),
                                              fromfile='a/hol/environment.ml', tofile='b/hol/environment.ml'))
    (destination / 'diagnostic-flags.patch').write_text(trace_patch)
    (destination / 'summary.json').write_text(json.dumps(records, indent=2, sort_keys=True) + '\n')
    print(json.dumps(records, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
