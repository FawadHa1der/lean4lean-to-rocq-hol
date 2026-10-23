#!/usr/bin/env python3
"""Record stable indexed-review inputs without starting or querying a server."""

from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
EXTRA = ['hol/indexed_tests.ml', 'frontend/wire.ml', 'frontend/replay.ml', 'frontend/hol_input.ml',
         'vendor/lean4lean/Lean4Lean/Inductive/Add.lean',
         'vendor/lean4lean/Lean4Lean/Inductive/Reduce.lean',
         'vendor/lean4lean/Lean4Lean/Replay.lean',
         'vendor/lean4lean/Lean4Lean/Environment/Basic.lean']
SEEDS = ['tutorial/043_eqType', 'tutorial/086_PSigma.snd', 'tutorial/076_sortElimPropRec',
         'tutorial/095_projDataIndexRec']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    target = HERE / 'snapshot'
    if target.exists():
        raise ValueError('refusing to overwrite the indexed audit snapshot')
    spec = importlib.util.spec_from_file_location('hol_snapshot', ROOT / 'scripts/hol-check.py')
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)
    before = runner.project_snapshot(ROOT)
    arena = json.loads((ROOT / 'arena/manifest.json').read_bytes())
    pins = []
    for case_id in SEEDS:
        entry, = [item for item in arena['cases'] if item['id'] == case_id]
        pin = {key: entry[key] for key in ('id', 'path', 'sha256', 'size')}
        if pin['size'] > 32768:
            raise ValueError('seed exceeds small-fixture bound')
        data = (ROOT / 'arena' / pin['path']).read_bytes()
        if len(data) != pin['size'] or digest(data) != pin['sha256']:
            raise ValueError('Arena seed pin mismatch')
        pins.append(pin)
    paths = sorted(set(EXTRA) | {entry['path'] for entry in before['inputs']}
                   | {'arena/' + pin['path'] for pin in pins})
    data = {relative: (ROOT / relative).read_bytes() for relative in paths}
    if any(len(content) > 2 * 1024 * 1024 for content in data.values()):
        raise ValueError('snapshot file exceeds bound')
    runner.require_stable_startup(before, runner.project_snapshot(ROOT))
    if any((ROOT / relative).read_bytes() != content for relative, content in data.items()):
        raise ValueError('review input changed during capture')
    old_path = ROOT / 'build/reports/hol-family-runtime.json'
    old_raw = old_path.read_bytes()
    old = json.loads(old_raw)
    old_inputs = {entry['path']: entry['sha256'] for entry in old['snapshot']['inputs']}
    entries = [{'path': path, 'size_bytes': len(content), 'sha256': digest(content),
                'old_family_startup_match': digest(content) == old_inputs[path] if path in old_inputs else None}
               for path, content in data.items()]
    manifest = {'version': 1, 'captured_at': datetime.now(timezone.utc).isoformat(),
                'upstream_revision': subprocess.check_output(
                    ['git', '-C', str(ROOT / 'vendor/lean4lean'), 'rev-parse', 'HEAD'], text=True).strip(),
                'inputs': entries, 'arena_source_pins': pins,
                'old_family_provenance_sha256': digest(old_raw),
                'runtime_identity': 'distinct-source-snapshot; no indexed warm server used',
                'scope': 'Filesystem source review, not execution or semantic attestation.'}
    target.mkdir(mode=0o700)
    for relative, content in data.items():
        path = target / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    (target / 'old-family-provenance.json').write_bytes(old_raw)
    (target / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'files': len(entries), 'seeds': len(pins),
                      'manifest_sha256': digest((target / 'manifest.json').read_bytes()),
                      'changed_from_old_family_startup': [e['path'] for e in entries
                                                           if e['old_family_startup_match'] is False]}))


if __name__ == '__main__':
    main()
