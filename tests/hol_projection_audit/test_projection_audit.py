"""Offline construction/accounting checks; these are not logical verdicts."""

import copy
import json
from pathlib import Path
import tempfile
import unittest

import projection_audit as suite
from test_metadata_mutations import classify


def decode(rows):
    names, levels, expressions, declarations = {0: ()}, {0: ('zero',)}, {}, []

    def header(h):
        out = copy.deepcopy(h)
        out.update(name=names[h['name']], levelParams=[names[n] for n in h['levelParams']],
                   type=expressions[h['type']])
        for field in ('all', 'ctors'):
            if field in h:
                out[field] = [names[n] for n in h[field]]
        if 'induct' in h:
            out['induct'] = names[h['induct']]
        if 'value' in h:
            out['value'] = expressions[h['value']]
        if 'rules' in h:
            out['rules'] = [(names[r['ctor']], r['nfields'], expressions[r['rhs']]) for r in h['rules']]
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
            assert row['ie'] not in expressions
            if 'bvar' in row:
                t = ('var', row['bvar'])
            elif 'sort' in row:
                t = ('sort', levels[row['sort']])
            elif 'const' in row:
                p = row['const']
                t = ('const', names[p['name']], tuple(levels[u] for u in p['us']))
            elif 'app' in row:
                p = row['app']
                t = ('app', expressions[p['fn']], expressions[p['arg']])
            elif 'proj' in row:
                p = row['proj']
                assert p['idx'] >= 0
                t = ('proj', names[p['typeName']], p['idx'], expressions[p['struct']])
            else:
                tag = next(k for k in ('lam', 'forallE') if k in row)
                p = row[tag]
                names[p['name']]
                t = (tag, expressions[p['type']], expressions[p['body']])
            expressions[row['ie']] = t
        elif 'inductive' in row:
            declarations.append(('inductive', {g: [header(h) for h in row['inductive'][g]]
                                                for g in ('types', 'ctors', 'recs')}))
        elif any(k in row for k in ('def', 'thm')):
            tag = 'def' if 'def' in row else 'thm'
            declarations.append((tag, header(row[tag])))
        else:
            assert 'meta' in row
    return declarations


def closed(term, depth=0):
    if term[0] == 'var':
        return 0 <= term[1] < depth
    if term[0] in ('sort', 'const'):
        return True
    if term[0] == 'proj':
        return closed(term[3], depth)
    if term[0] == 'app':
        return closed(term[1], depth) and closed(term[2], depth)
    return closed(term[1], depth) and closed(term[2], depth + 1)


def unbind(term, tag='forallE'):
    domains = []
    while term[0] == tag:
        domains.append(term[1])
        term = term[2]
    return domains, term


class ProjectionAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest, cls.files = suite.plan()

    def declarations(self, path):
        return decode(suite.builder.rows_of(self.files[path]))

    def test_deterministic_bounded_hashed_plan(self):
        self.assertEqual((self.manifest, self.files), suite.plan())
        self.assertEqual(len(self.manifest['baselines']), 8)
        self.assertEqual(len(self.manifest['cases']), 76)
        self.assertEqual(sum(c['expected'] == 'accept' for c in self.manifest['cases']), 30)
        for entry in self.manifest['baselines'] + self.manifest['cases']:
            self.assertEqual(suite.sha(self.files[entry['path']]), entry['sha256'])
            self.assertEqual(len(self.files[entry['path']]), entry['size'])
            self.assertTrue(entry['rationale'])

    def test_genuine_seven_gates_are_byte_exact(self):
        for seed in suite.PINS['seeds']:
            family = Path(seed['path']).name[:3]
            raw = (suite.SNAPSHOT / 'arena' / seed['path']).read_bytes()
            self.assertEqual(self.files['baselines/' + family + '.ndjson'], raw)
            self.assertEqual(self.files['cases/' + family + '/unchanged.ndjson'], raw)

    def test_all_table_references_and_closed_terms(self):
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
                        terms += [h['type'], h['value']]
                self.assertTrue(all(closed(t) for t in terms))

    def test_transport_controls_preserve_canonical_declarations(self):
        for family in suite.TARGETS:
            original = self.declarations('baselines/' + family + '.ndjson')
            self.assertEqual(original, self.declarations('cases/' + family + '/anonymous-binders.ndjson'))
            self.assertEqual(original, list(reversed(self.declarations('cases/' + family + '/forward-declarations.ndjson'))))

    def test_path_copy_preserves_inductive_claims(self):
        for family in suite.TARGETS:
            def blocks(path):
                return [d for tag, d in self.declarations(path) if tag == 'inductive']
            original = blocks('baselines/' + family + '.ndjson')
            for mode in ('owner-constructor', 'owner-unknown', 'index-boundary', 'major-sort'):
                self.assertEqual(original, blocks('cases/' + family + '/' + mode + '.ndjson'))

    def test_psigma_debruijn_contexts(self):
        h = self.declarations('baselines/086-dependent.ndjson')[-1][1]
        domains, result = unbind(h['type'])
        self.assertEqual(domains[4], ('app', ('var', 2), ('var', 1)))  # b : B a
        self.assertEqual(domains[5], ('app', ('var', 3), ('var', 1)))  # otherb : B other
        self.assertEqual(result, ('app', ('var', 4), ('var', 3)))
        _, value = unbind(h['value'], 'lam')
        self.assertEqual(value[0:3], ('proj', ('PSigma',), 1))
        bad = self.declarations('cases/086-dependent/wrong-dependent-field.ndjson')[-1][1]
        self.assertEqual(h['type'], bad['type'])
        self.assertNotEqual(h['value'], bad['value'])

    def test_prop_dependency_is_not_an_invented_field(self):
        block = [d for tag, d in self.declarations('baselines/089.ndjson') if tag == 'inductive'][-1]
        domains, result = unbind(block['ctors'][0]['type'])
        self.assertEqual(len(domains), 6)
        self.assertEqual(domains[0], domains[2])
        self.assertEqual(domains[0], domains[5])
        self.assertEqual(domains[1], domains[3])
        self.assertEqual(domains[4][-1], ('var', 0))
        self.assertEqual(domains[4][1][-1], ('var', 0))  # Eq ... field3 field3
        self.assertEqual(result[0:2], ('const', ('PropStructure',)))

    def test_derived_gate_keeps_complete_genuine_export(self):
        base = self.declarations('baselines/086.ndjson')
        derived = self.declarations('baselines/086-dependent.ndjson')
        self.assertEqual(base, derived[:-1])
        self.assertEqual(self.files['baselines/086-dependent.ndjson'],
                         self.files['cases/086-dependent/control.ndjson'])

    def test_failed_gates_never_count_as_rejections(self):
        small = {'baselines': [{'id': 'b', 'family': 'f', 'path': 'baseline', 'sha256': 'h'}],
                 'cases': [{'id': 'c', 'family': 'f', 'path': 'case', 'sha256': 'h',
                            'expected': 'reject', 'dimension': 'owner'}]}
        for code in (1, 2, 3):
            calls = []
            def fake(command, *args):
                calls.append(command)
                return {'exit_code': code, 'timed_out': False}
            report = suite.run_suite(small, Path('/private/tmp'), ['dummy'], 1, 32, execute=fake)
            self.assertEqual(len(calls), 1)
            self.assertEqual(report['cases'][0]['status'], 'not_covered')
        self.assertEqual(classify({'exit_code': 2}, 'reject'), 'declined')
        self.assertEqual(classify({'exit_code': 0}, 'reject'), 'false_accept')
        self.assertEqual(classify({'exit_code': 1}, 'reject'), 'correct_reject')

    def test_report_no_overwrite(self):
        with tempfile.TemporaryDirectory(dir='/private/tmp') as temp:
            path = Path(temp) / 'report.json'
            suite.atomic_report(path, {'test_only': True})
            self.assertEqual(json.loads(path.read_bytes()), {'test_only': True})
            self.assertEqual(path.stat().st_mode & 0o777, 0o600)
            with self.assertRaises(ValueError):
                suite.atomic_report(path, {'changed': True})

    def test_recursor_probe_specialization_is_local_and_coherent(self):
        import diagnose_recursor_exports as probes
        manifest, files = probes.plan()
        self.assertEqual(len(manifest['cases']), 4)
        self.assertEqual(len(manifest['baselines']), 2)
        self.assertLessEqual(len(manifest['cases']) + len(self.manifest['cases']), 80)
        def subst(t):
            if t == ('param', ('u',)):
                return ('zero',)
            if isinstance(t, tuple):
                return tuple(subst(v) for v in t)
            return t
        for name in probes.PINS:
            original = decode(suite.builder.rows_of(files['cases/' + name + '-original.ndjson']))
            specialized = decode(suite.builder.rows_of(files['cases/' + name + '-universe-zero.ndjson']))
            self.assertEqual(original[:-1], specialized[:-1])
            first, second = original[-1][1], specialized[-1][1]
            self.assertEqual(first['levelParams'], [('u',)])
            self.assertEqual(second['levelParams'], [])
            for key in ('type', 'value'):
                self.assertEqual(subst(first[key]), second[key])
                self.assertTrue(closed(second[key]))


if __name__ == '__main__':
    unittest.main()
