"""Offline fixture/accounting checks, not a logical verdict oracle."""

import copy
import json
from pathlib import Path
import tempfile
import unittest

import quotient_audit as suite


def decode(rows):
    names, levels, exprs, decls = {0: ()}, {0: ('zero',)}, {}, []
    def header(h):
        out = copy.deepcopy(h)
        out.update(name=names[h['name']], levelParams=[names[n] for n in h['levelParams']], type=exprs[h['type']])
        for field in ('all', 'ctors'):
            if field in h:
                out[field] = [names[n] for n in h[field]]
        if 'induct' in h:
            out['induct'] = names[h['induct']]
        if 'value' in h:
            out['value'] = exprs[h['value']]
        if 'rules' in h:
            out['rules'] = [(names[r['ctor']], r['nfields'], exprs[r['rhs']]) for r in h['rules']]
        return out
    for row in rows:
        if 'in' in row:
            assert row['in'] not in names
            p = row.get('str', row.get('num'))
            names[row['in']] = names[p['pre']] + (p['str'] if 'str' in row else p['i'],)
        elif 'il' in row:
            assert row['il'] not in levels
            if 'param' in row:
                t = ('param', names[row['param']])
            elif 'succ' in row:
                t = ('succ', levels[row['succ']])
            else:
                tag = 'max' if 'max' in row else 'imax'
                t = (tag, *(levels[v] for v in row[tag]))
            levels[row['il']] = t
        elif 'ie' in row:
            assert row['ie'] not in exprs
            if 'bvar' in row:
                t = ('var', row['bvar'])
            elif 'sort' in row:
                t = ('sort', levels[row['sort']])
            elif 'const' in row:
                p = row['const']
                t = ('const', names[p['name']], tuple(levels[v] for v in p['us']))
            elif 'app' in row:
                t = ('app', exprs[row['app']['fn']], exprs[row['app']['arg']])
            else:
                tag = next(k for k in ('forallE', 'lam') if k in row)
                p = row[tag]
                names[p['name']]
                t = (tag, exprs[p['type']], exprs[p['body']])
            exprs[row['ie']] = t
        elif 'inductive' in row:
            decls.append(('inductive', {g: [header(h) for h in row['inductive'][g]] for g in ('types', 'ctors', 'recs')}))
        elif 'meta' not in row:
            tag, h = next(iter(row.items()))
            assert tag in ('quot', 'def', 'thm', 'axiom')
            decls.append((tag, header(h)))
    return decls


def closed(t, depth=0):
    if t[0] == 'var':
        return 0 <= t[1] < depth
    if t[0] in ('sort', 'const'):
        return True
    return closed(t[1], depth) and closed(t[2], depth + (t[0] != 'app'))


def unbind(t, tag='forallE'):
    domains = []
    while t[0] == tag:
        domains.append(t[1])
        t = t[2]
    return domains, t


class QuotientAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest, cls.files = suite.plan()

    def declarations(self, path):
        return decode(suite.builder.rows_of(self.files[path]))

    def test_deterministic_bounds_and_hashes(self):
        self.assertEqual((self.manifest, self.files), suite.plan())
        self.assertEqual(len(self.manifest['cases']), 68)
        self.assertEqual(len(self.manifest['baselines']), 8)
        self.assertEqual(sum(c['expected'] == 'accept' for c in self.manifest['cases']), 25)
        for e in self.manifest['baselines'] + self.manifest['cases']:
            self.assertEqual(suite.sha(self.files[e['path']]), e['sha256'])
            self.assertEqual(len(self.files[e['path']]), e['size'])
            self.assertTrue(e['rationale'])

    def test_actual_seeds_and_unchanged_controls(self):
        for seed in suite.PINS['seeds']:
            family = Path(seed['path']).name[:3]
            original = (suite.SNAPSHOT / 'arena' / seed['path']).read_bytes()
            self.assertEqual(original, self.files['baselines/' + family + '.ndjson'])
            self.assertEqual(original, self.files['cases/' + family + '/unchanged.ndjson'])

    def test_all_references_and_scopes(self):
        for path in self.files:
            with self.subTest(path=path):
                terms = []
                for tag, h in self.declarations(path):
                    if tag == 'inductive':
                        for group in h.values():
                            for d in group:
                                terms.append(d['type'])
                                terms += [r[2] for r in d.get('rules', [])]
                    else:
                        terms.append(h['type'])
                        if 'value' in h:
                            terms.append(h['value'])
                self.assertTrue(all(closed(t) for t in terms))

    def test_transport_controls_preserve_canonical_terms(self):
        for family in ('126', '127', '128', '129', '130', '131'):
            original = self.declarations('baselines/' + family + '.ndjson')
            self.assertEqual(original, self.declarations('cases/' + family + '/anonymous-binders.ndjson'))
            self.assertEqual(original, list(reversed(self.declarations('cases/' + family + '/forward-declarations.ndjson'))))

    def test_reconstructed_reduction_theorems_match_actual_exports(self):
        for family in ('130', '131'):
            self.assertEqual(self.declarations('baselines/' + family + '.ndjson'),
                             self.declarations('cases/' + family + '/canonical.ndjson'))

    def test_canonical_eq_reconstruction_matches_actual(self):
        seed = suite.PINS['seeds'][0]
        rows, _ = suite.seed_rows(seed)
        original = [d for tag, d in decode(rows) if tag == 'inductive']
        self.assertEqual(original, [d for tag, d in decode(suite.equality_variant(rows)) if tag == 'inductive'])

    def test_coherent_eq_gates_preserve_metadata_relationships(self):
        for kind, fields, result in (('any-constructor', 1, ('sort', ('zero',))),
                                      ('type-valued', 0, ('sort', ('succ', ('zero',))))):
            gate = self.declarations('baselines/eq-' + kind + '.ndjson')
            case = self.declarations('cases/eq-' + kind + '/quotient-prerequisite.ndjson')
            self.assertEqual(gate, case[:1])
            self.assertEqual([t for t, _ in case], ['inductive', 'quot', 'quot', 'quot', 'quot'])
            block = gate[0][1]
            ind, ctor, rec = block['types'][0], block['ctors'][0], block['recs'][0]
            self.assertEqual(unbind(ind['type'])[1], result)
            self.assertEqual(ctor['numFields'], fields)
            self.assertEqual(rec['rules'][0][1], fields)
            self.assertFalse(rec['k'])
            self.assertEqual(ctor['induct'], ind['name'])
            self.assertEqual(ind['ctors'], [ctor['name']])

    def test_header_path_copy_and_name_structure(self):
        original = self.declarations('baselines/126.ndjson')
        changed = self.declarations('cases/126/lift-first-domain-prop.ndjson')
        differences = [(a, b) for a, b in zip(original, changed) if a != b]
        self.assertEqual(len(differences), 1)
        self.assertEqual(differences[0][0][1]['kind'], 'lift')
        dotted = self.declarations('cases/126/ctor-dotted-single-name.ndjson')
        self.assertIn(('Quot.mk',), [h['name'] for tag, h in dotted if tag == 'quot'])
        self.assertNotIn(('Quot', 'mk'), [h['name'] for tag, h in dotted if tag == 'quot'])

    def test_quotient_universe_control_preserves_generated_eq(self):
        original = self.declarations('baselines/126.ndjson')
        renamed = self.declarations('cases/126/universe-alpha-renamed.ndjson')
        self.assertEqual(original[0], renamed[0])
        self.assertEqual(original[0][0], 'inductive')
        lift_before = next(h for t, h in original if t == 'quot' and h['kind'] == 'lift')
        lift_after = next(h for t, h in renamed if t == 'quot' and h['kind'] == 'lift')
        self.assertEqual(lift_before['levelParams'][0], lift_after['levelParams'][0])
        self.assertNotEqual(lift_before['levelParams'][1], lift_after['levelParams'][1])

    def test_no_new_object_axioms(self):
        for entry in self.manifest['baselines'] + self.manifest['cases']:
            axioms = [h for tag, h in self.declarations(entry['path']) if tag == 'axiom']
            if entry['family'] == '129':
                self.assertEqual([h['name'] for h in axioms], [('Quot', 'sound')])
            else:
                self.assertEqual(axioms, [])

    def test_invalid_claims_are_not_mislabeled_as_upstream_replay_rejections(self):
        headers = [c for c in self.manifest['cases'] if c['dimension'] == 'header']
        self.assertEqual(len(headers), 28)
        self.assertEqual(sum(c['expectation_basis'] == 'claim-integrity' for c in headers), 27)
        self.assertEqual(sum(c['expectation_basis'] == 'malformed' for c in headers), 1)
        control = next(c for c in self.manifest['cases'] if c['id'] == '131/neutral-major-proof-control')
        self.assertEqual((control['expected'], control['expectation_basis']), ('accept', 'proof-irrelevance'))

    def test_multiple_gates_and_decline_accounting(self):
        manifest = {'baselines': [{'id': k, 'family': k, 'path': k, 'sha256': k} for k in ('canonical', 'altered')],
                    'cases': [{'id': 'c', 'family': 'altered', 'path': 'case', 'sha256': 'h',
                               'expected': 'reject', 'dimension': 'eq', 'expectation_basis': 'typing',
                               'requires': ['canonical', 'altered']}]}
        for failed in ('canonical', 'altered'):
            calls = []
            def fake(command, *args):
                calls.append(command[-1])
                return {'exit_code': 2 if Path(command[-1]).name == failed else 0}
            report = suite.run_suite(manifest, Path('/private/tmp'), ['dummy'], 1, execute=fake)
            self.assertEqual(len(calls), 2)
            self.assertEqual(report['cases'][0]['status'], 'not_covered')
            self.assertEqual(report['cases'][0]['failed_gates'], [failed])
        for code, status in ((0, 'false_accept'), (1, 'correct_reject'), (2, 'declined'), (3, 'fault')):
            def fake(command, *args):
                return {'exit_code': code if Path(command[-1]).name == 'case' else 0}
            report = suite.run_suite(manifest, Path('/private/tmp'), ['dummy'], 1, execute=fake)
            self.assertEqual(report['cases'][0]['status'], status)

    def test_private_report_refuses_overwrite(self):
        with tempfile.TemporaryDirectory(dir='/private/tmp') as temp:
            path = Path(temp) / 'report.json'
            suite.atomic_report(path, {'offline_test_only': True})
            self.assertEqual(path.stat().st_mode & 0o777, 0o600)
            self.assertEqual(json.loads(path.read_bytes()), {'offline_test_only': True})
            with self.assertRaises(ValueError):
                suite.atomic_report(path, {'changed': True})


if __name__ == '__main__':
    unittest.main()
