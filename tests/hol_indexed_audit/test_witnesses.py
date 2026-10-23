"""Offline checks of fixture construction and coverage accounting, not an oracle."""

import copy
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import witnesses as suite


def decode(rows):
    names, levels, exprs, decls = {0: ()}, {0: ('zero',)}, {}, []

    def header(h):
        result = copy.deepcopy(h)
        result.update(name=names[h['name']], levelParams=[names[n] for n in h['levelParams']], type=exprs[h['type']])
        for field in ('all', 'ctors'):
            if field in h:
                result[field] = [names[n] for n in h[field]]
        if 'induct' in h:
            result['induct'] = names[h['induct']]
        if 'value' in h:
            result['value'] = exprs[h['value']]
        if 'rules' in h:
            result['rules'] = [(names[r['ctor']], r['nfields'], exprs[r['rhs']]) for r in h['rules']]
        return result

    for row in rows:
        if 'in' in row:
            assert row['in'] not in names
            p = row.get('str', row.get('num'))
            names[row['in']] = names[p['pre']] + (p['str'] if 'str' in row else p['i'],)
        elif 'il' in row:
            assert row['il'] not in levels
            if 'param' in row:
                term = ('param', names[row['param']])
            elif 'succ' in row:
                term = ('succ', levels[row['succ']])
            else:
                tag = 'max' if 'max' in row else 'imax'
                term = (tag, *(levels[u] for u in row[tag]))
            levels[row['il']] = term
        elif 'ie' in row:
            assert row['ie'] not in exprs
            if 'bvar' in row:
                term = ('var', row['bvar'])
            elif 'sort' in row:
                term = ('sort', levels[row['sort']])
            elif 'const' in row:
                term = ('const', names[row['const']['name']], tuple(levels[u] for u in row['const']['us']))
            elif 'app' in row:
                term = ('app', exprs[row['app']['fn']], exprs[row['app']['arg']])
            elif 'proj' in row:
                p = row['proj']
                term = ('proj', names[p['typeName']], p['idx'], exprs[p['struct']])
            else:
                tag = next(t for t in ('forallE', 'lam') if t in row)
                p = row[tag]
                names[p['name']]
                term = (tag, exprs[p['type']], exprs[p['body']])
            exprs[row['ie']] = term
        elif 'inductive' in row:
            decls.append(('inductive', {g: [header(h) for h in row['inductive'][g]] for g in ('types', 'ctors', 'recs')}))
        elif 'def' in row:
            decls.append(('def', header(row['def'])))
        else:
            assert 'meta' in row
    return decls


def closed(e, depth=0):
    tag = e[0]
    if tag == 'var':
        return 0 <= e[1] < depth
    if tag in ('sort', 'const'):
        return True
    if tag == 'proj':
        return closed(e[3], depth)
    if tag == 'app':
        return closed(e[1], depth) and closed(e[2], depth)
    return closed(e[1], depth) and closed(e[2], depth + 1)


def telescope(e, tag='forallE'):
    domains = []
    while e[0] == tag:
        domains.append(e[1])
        e = e[2]
    return domains, e


class IndexedWitnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest, cls.files = suite.plan()

    def rows(self, path):
        return suite.rows_of(self.files[path])

    def subject(self, path):
        return [d for tag, d in decode(self.rows(path)) if tag == 'inductive'][-1]

    def test_hashes_determinism_and_no_duplicate_case_bytes(self):
        self.assertEqual((self.manifest, self.files), suite.plan())
        self.assertEqual(len(self.manifest['baselines']), 7)
        self.assertGreaterEqual(len(self.manifest['cases']), 60)
        for e in self.manifest['baselines'] + self.manifest['cases']:
            self.assertEqual(suite.sha(self.files[e['path']]), e['sha256'])
            self.assertEqual(len(self.files[e['path']]), e['size'])
        self.assertEqual(len({e['sha256'] for e in self.manifest['cases']}), len(self.manifest['cases']))

    def test_references_and_scope(self):
        for path in self.files:
            terms = []
            for tag, d in decode(self.rows(path)):
                if tag == 'def':
                    terms += [d['type'], d['value']]
                else:
                    for group in d.values():
                        for h in group:
                            terms.append(h['type'])
                            terms += [r[2] for r in h.get('rules', [])]
            with self.subTest(path=path):
                self.assertEqual(all(closed(t) for t in terms), not any(
                    label in path for label in ('snd-out-of-context', 'index-context-overflow')))

    def test_baselines_are_genuine_exports_or_documented_derivations(self):
        aliases = {'eq': '043_eqType', 'psigma': '086_PSigma.snd',
                   'sortelim': '076_sortElimPropRec', 'proof-field': '095_projDataIndexRec'}
        for family, filename in aliases.items():
            original = suite.rows_of((HERE / 'snapshot/arena/corpus/tutorial' / (filename + '.ndjson')).read_bytes())
            if family == 'psigma':
                original = suite.admission_only(original)
            self.assertEqual(self.rows('baselines/' + family + '.ndjson'), original)
        original = self.subject('baselines/sortelim.ndjson')
        rebuilt = self.subject('baselines/sortelim-coherent.ndjson')
        self.assertEqual(original, rebuilt)

    def test_dependent_field_context_and_path_copy(self):
        original = self.subject('baselines/psigma.ndjson')
        domains, _ = telescope(original['ctors'][0]['type'])
        self.assertEqual(domains[2], ('var', 1))  # A, before the first field.
        self.assertEqual(domains[3], ('app', ('var', 1), ('var', 0)))  # B a, before the second.
        changed = self.subject('cases/psigma/snd-captures-field.ndjson')
        self.assertEqual(original['types'], changed['types'])
        self.assertEqual(original['recs'], changed['recs'])
        self.assertNotEqual(original['ctors'][0]['type'], changed['ctors'][0]['type'])
        minor_domains, _ = telescope(original['recs'][0]['type'])
        field_domains, _ = telescope(minor_domains[3])
        self.assertEqual(field_domains[1], ('app', ('var', 2), ('var', 0)))  # B moves over motive, a does not.

    def test_eq_indices_and_k_golden(self):
        eq = self.subject('baselines/eq.ndjson')
        self.assertTrue(eq['recs'][0]['k'])
        self.assertEqual(eq['ctors'][0]['numFields'], 0)
        _, result = telescope(eq['ctors'][0]['type'])
        self.assertEqual(result[-1], ('var', 0))
        self.assertFalse(self.subject('baselines/proof-field.ndjson')['recs'][0]['k'])

    def test_coherent_large_elimination_variants(self):
        base = self.subject('baselines/sortelim-coherent.ndjson')
        for label in ('hidden-data-forged-large', 'nested-index-forged-large'):
            changed = self.subject('cases/sortelim-coherent/' + label + '.ndjson')
            self.assertEqual(changed['types'], base['types'])
            self.assertNotEqual(changed['ctors'][0]['type'], base['ctors'][0]['type'])
            self.assertNotEqual(changed['recs'][0]['type'], base['recs'][0]['type'])
            self.assertNotEqual(changed['recs'][0]['rules'], base['recs'][0]['rules'])
            self.assertEqual(changed['recs'][0]['levelParams'], base['recs'][0]['levelParams'])
        for label in ('hidden-data-prop-only', 'nested-index-prop-only'):
            self.assertEqual(self.subject('cases/sortelim-coherent/' + label + '.ndjson')['recs'][0]['levelParams'], [])

    def test_runtime_comparison_checks_all_recorded_inputs(self):
        import json
        entries = suite.snapshot()['inputs']
        mock = {'snapshot': {'inputs': [{'path': e['path'], 'sha256': e['sha256']} for e in entries]}}
        self.assertTrue(suite.runtime_comparison(json.dumps(mock).encode())['all_runtime_project_inputs_match_review'])
        mock['snapshot']['inputs'][0]['sha256'] = '0' * 64
        self.assertFalse(suite.runtime_comparison(json.dumps(mock).encode())['all_runtime_project_inputs_match_review'])

    def test_baseline_gates_and_declines(self):
        calls = []

        def decline(command, path, timeout, mode, limit):
            calls.append(path)
            return {'exit_code': 2, 'timed_out': False}

        report = suite.run_suite(self.manifest, HERE, ['unused'], 1, 20, execute=decline)
        self.assertEqual(len(calls), 7)
        self.assertEqual(report['summary']['covered'], 0)
        self.assertEqual(report['summary']['statuses'], {'not_covered': len(self.manifest['cases'])})

        def decline_cases(command, path, timeout, mode, limit):
            return {'exit_code': 0 if 'baselines' in path.parts else 2, 'timed_out': False}

        report = suite.run_suite(self.manifest, HERE, ['unused'], 1, 20, execute=decline_cases)
        self.assertEqual(report['summary']['covered'], 0)
        self.assertEqual(report['summary']['statuses'], {'declined': len(self.manifest['cases'])})


if __name__ == '__main__':
    unittest.main()
