#!/usr/bin/env python3
"""Capture a bounded read-only audit snapshot; never start HOL or alter sources."""

import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
EXTRA = ['hol/family_tests.ml', 'hol/inductive_tests.ml', 'frontend/wire.ml',
         'frontend/replay.ml', 'frontend/hol_input.ml',
         'vendor/lean4lean/Lean4Lean/Inductive/Add.lean',
         'vendor/lean4lean/Lean4Lean/Inductive/Reduce.lean',
         'vendor/lean4lean/Lean4Lean/TypeChecker.lean',
         'vendor/lean4lean/Lean4Lean/Replay.lean',
         'vendor/lean4lean/Lean4Lean/Environment/Basic.lean',
         'vendor/lean4lean/Lean4Lean/Primitive.lean']


def main():
    target = HERE / 'snapshot'
    if target.exists():
        raise ValueError('audit snapshot already exists; never overwrite')
    spec = importlib.util.spec_from_file_location('hol_runner_audit', ROOT / 'scripts/hol-check.py')
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)
    before = runner.project_snapshot(ROOT)
    startup_path = ROOT / 'build/reports/hol-family-runtime.json'
    startup_bytes = startup_path.read_bytes()
    startup = json.loads(startup_bytes)
    loaded = {entry['path']: entry for entry in startup['snapshot']['inputs']}
    contents, entries = {}, []
    paths = sorted(set(EXTRA) | {entry['path'] for entry in before['inputs']})
    for relative in paths:
        data = (ROOT / relative).read_bytes()
        if len(data) > 2 * 1024 * 1024:
            raise ValueError('audit input exceeds size bound: ' + relative)
        contents[relative] = data
        digest = hashlib.sha256(data).hexdigest()
        entry = {'path': relative, 'sha256': digest, 'size_bytes': len(data),
                 'startup_match': digest == loaded[relative]['sha256'] if relative in loaded else None}
        entries.append(entry)
    runner.require_stable_startup(before, runner.project_snapshot(ROOT))
    for relative, data in contents.items():
        if (ROOT / relative).read_bytes() != data:
            raise ValueError('audit input changed during capture: ' + relative)
    mismatches = [entry['path'] for entry in entries if entry['startup_match'] is False]
    manifest = {
        'version': 1, 'captured_at': datetime.now(timezone.utc).isoformat(),
        'upstream_revision': subprocess.check_output(
            ['git', '-C', str(ROOT / 'vendor/lean4lean'), 'rev-parse', 'HEAD'], text=True).strip(),
        'startup_manifest': 'build/reports/hol-family-runtime.json',
        'startup_manifest_sha256': hashlib.sha256(startup_bytes).hexdigest(),
        'startup_input_comparison': 'matching-project-inputs' if not mismatches else 'distinct-source-snapshot',
        'startup_mismatches': mismatches, 'inputs': entries,
        'scope': 'Source review snapshot; no runtime or semantic attestation. Extra source files may not identify bytecode build inputs.',
    }
    target.mkdir(mode=0o700)
    try:
        for relative, data in contents.items():
            path = target / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        (target / 'startup-provenance.json').write_bytes(startup_bytes)
        (target / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    except BaseException:
        shutil.rmtree(target)
        raise
    print(json.dumps({'snapshot': str(target), 'files': len(entries),
                      'startup_input_comparison': manifest['startup_input_comparison'],
                      'mismatches': mismatches}, sort_keys=True))


if __name__ == '__main__':
    main()
