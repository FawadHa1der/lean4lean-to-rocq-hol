#!/usr/bin/env python3
"""Assemble recorded observations by exact input hash; never invokes a checker."""

import json
import quotient_audit as suite

SOURCES = {
    'quotient-report.json': '3f5da567c17897233b470fbc97f81f481eccff774016c73a66a1b619d0819399',
    'universe-control-report.json': '1ff4cae85420df286c64f186bd7a131b2dd7948fead5b4ac076a80fddb094e7e'}
RUNTIME_SHA = '9edacc5e005ad863c595eedfeb947b38fdf3debb7db05afdffaa2b6e71517c67'


def assemble():
    manifest, files = suite.plan()
    suite.validate_materialized(suite.HERE / 'fixtures-final', manifest, files)
    reports = []
    for name, digest in SOURCES.items():
        raw = (suite.HERE / name).read_bytes()
        assert suite.sha(raw) == digest
        r = json.loads(raw)
        assert r['checker']['unchanged'] and r['runtime']['matches_review']
        assert r['runtime']['manifest_sha256'] == RUNTIME_SHA
        reports.append((digest, r))
    assert suite.sha((suite.HERE / 'initial-runner.py').read_bytes()) == '194e096b7f9eb7c3a9cb588ad24f88f3df48bab85cf9cb13db687e11fb34adf2'
    baselines, cases = [], []
    for group, output in (('baselines', baselines), ('cases', cases)):
        for entry in manifest[group]:
            observations = [(digest, row) for digest, r in reports for row in r[group]
                            if row['id'] == entry['id'] and row['sha256'] == entry['sha256']]
            assert observations, 'no observation for final fixture: ' + entry['id']
            digest, row = observations[-1]
            if group == 'cases':
                assert all(row[k] == entry[k] for k in ('expected', 'requires', 'expectation_basis'))
                assert row['status'] == suite.classify(row, entry['expected'])
            output.append({**row, 'observation_report_sha256': digest})
    gates = {b['family']: b for b in baselines}
    for case in cases:
        assert all(gates[g]['status'] == 'accepted' for g in case['requires'])
    excluded = next(c for c in reports[0][1]['cases'] if c['id'] == '126/universe-alpha-renamed')
    assert excluded['sha256'] != next(c['sha256'] for c in cases if c['id'] == excluded['id'])
    return {'version': 1, 'kind': 'hash-verified-observation-aggregation',
            'created_at': suite.utc_now(), 'runtime_calls_by_assembler': 0,
            'runtime_provenance_sha256': RUNTIME_SHA, 'review_snapshot_sha256': suite.SNAPSHOT_SHA,
            'manifest_sha256': suite.sha(suite.json_bytes(manifest)), 'source_reports': SOURCES,
            'baselines': baselines, 'cases': cases, 'summary': suite.summarize(baselines, cases),
            'withdrawn_initial_control': {**excluded,
                'reason': 'Whole-export universe renaming also changed Eq.rec generated fresh universe. Pinned Inductive/Add.lean:280-287 regenerates u; Replay.lean:247-249 compares recursor metadata. This is not a valid positive transport control; the revised fixture preserves the generated Eq block.'},
            'limitations': ['A recorded decline is not a refutation.',
                            'The sole code-1 result is an unknown metadata discriminator, not a logical refutation.',
                            'Quot.sound remains an explicit object assumption only in the authentic 129 family.',
                            'No proof of soundness/completeness or dynamic runtime attestation.']}


if __name__ == '__main__':
    report = assemble()
    suite.atomic_report(suite.HERE / 'final-report.json', report)
    print(json.dumps(report['summary'], sort_keys=True))
