import copy
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import witnesses as suite


def decode(rows):
    names, levels, exprs, declarations = {0: ()}, {0: ('zero',)}, {}, []

    def header(item):
        result = copy.deepcopy(item)
        result.update(name=names[item['name']], levelParams=[names[n] for n in item['levelParams']],
                      type=exprs[item['type']])
        for field in ('all', 'ctors'):
            if field in item:
                result[field] = [names[n] for n in item[field]]
        if 'induct' in item:
            result['induct'] = names[item['induct']]
        if 'value' in item:
            result['value'] = exprs[item['value']]
        if 'rules' in item:
            result['rules'] = [(names[r['ctor']], r['nfields'], exprs[r['rhs']]) for r in item['rules']]
        return result

    for row in rows:
        if 'in' in row:
            assert row['in'] not in names
            names[row['in']] = names[row['str']['pre']] + (row['str']['str'],)
        elif 'il' in row:
            assert row['il'] not in levels
            levels[row['il']] = ('succ', levels[row['succ']]) if 'succ' in row else ('param', names[row['param']])
        elif 'ie' in row:
            assert row['ie'] not in exprs
            if 'bvar' in row:
                value = ('var', row['bvar'])
            elif 'sort' in row:
                value = ('sort', levels[row['sort']])
            elif 'const' in row:
                value = ('const', names[row['const']['name']], tuple(levels[u] for u in row['const']['us']))
            elif 'app' in row:
                value = ('app', exprs[row['app']['fn']], exprs[row['app']['arg']])
            else:
                tag = next(t for t in ('lam', 'forallE') if t in row)
                names[row[tag]['name']]
                value = (tag, exprs[row[tag]['type']], exprs[row[tag]['body']])
            exprs[row['ie']] = value
        elif 'inductive' in row:
            declarations.append(('inductive', {k: [header(d) for d in row['inductive'][k]]
                                                 for k in ('types', 'ctors', 'recs')}))
        elif 'def' in row:
            declarations.append(('def', header(row['def'])))
        else:
            assert 'meta' in row
    return declarations


def closed(expr, depth=0):
    if expr[0] == 'var':
        return 0 <= expr[1] < depth
    if expr[0] in ('sort', 'const'):
        return True
    if expr[0] == 'app':
        return closed(expr[1], depth) and closed(expr[2], depth)
    return closed(expr[1], depth) and closed(expr[2], depth + 1)


class FamilyWitnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest, cls.files = suite.plan()

    def rows(self, relative):
        return [json.loads(line) for line in self.files[relative].splitlines()]

    def test_deterministic_plan_hashes_and_expectations(self):
        self.assertEqual((self.manifest, self.files), suite.plan())
        self.assertEqual(len(self.manifest['baselines']), 10)
        self.assertEqual(len(self.manifest['cases']), 41)
        self.assertEqual(suite.Counter(c['expected'] for c in self.manifest['cases']), {'accept': 10, 'reject': 31})
        for entry in self.manifest['baselines'] + self.manifest['cases']:
            self.assertEqual(entry['sha256'], suite.sha(self.files[entry['path']]))
            self.assertEqual(entry['size'], len(self.files[entry['path']]))

    def test_reference_order_and_closure_except_explicit_scope_negative(self):
        for path in self.files:
            terms = []
            for kind, value in decode(self.rows(path)):
                if kind == 'def':
                    terms += [value['type'], value['value']]
                else:
                    for group in value.values():
                        for entry in group:
                            terms.append(entry['type'])
                            terms += [r[2] for r in entry.get('rules', [])]
            with self.subTest(path=path):
                self.assertEqual(all(closed(term) for term in terms), 'out-of-scope-parameter' not in path)

    def test_independent_dependent_parameter_constructor_shape(self):
        block = decode(self.rows('baselines/dependent.ndjson'))[0][1]
        var = lambda n: ('var', n)
        pi = lambda a, b: ('forallE', a, b)
        app = lambda a, b: ('app', a, b)
        family = ('const', ('FamilyAudit', 'Dependent'), ())
        expected = pi(('sort', ('succ', ('zero',))), pi(var(0), pi(var(1), app(app(family, var(2)), var(1)))))
        self.assertEqual(block['ctors'][0]['type'], expected)

    def test_constructor_prefix_mutation_does_not_regenerate_other_claims(self):
        original = decode(self.rows('baselines/dependent.ndjson'))[0][1]
        changed = decode(self.rows('cases/dependent/mismatched-constructor-prefix.ndjson'))[0][1]
        self.assertEqual(original['ctors'], changed['ctors'])
        self.assertEqual(original['recs'], changed['recs'])
        self.assertNotEqual(original['types'][0]['type'], changed['types'][0]['type'])

    def test_independent_branching_recursive_rhs_indices(self):
        block = decode(self.rows('baselines/chain.ndjson'))[0][1]
        rhs = block['recs'][0]['rules'][1][2]
        domains = []
        while rhs[0] == 'lam':
            domains.append(rhs[1])
            rhs = rhs[2]
        self.assertEqual(len(domains), 7)  # A, motive, two minors, and three fields.
        var = lambda n: ('var', n)

        def apps(fn, *args):
            for arg in args:
                fn = ('app', fn, arg)
            return fn

        rec = ('const', ('FamilyAudit', 'Chain', 'rec'),
               (('param', ('u_1',)), ('param', ('u',))))
        prefix = apps(rec, var(6), var(5), var(4), var(3))
        expected = apps(var(3), var(2), var(1), var(0), apps(prefix, var(1)), apps(prefix, var(0)))
        self.assertEqual(rhs, expected)

    def test_order_controls_and_duplicate_substitution(self):
        original = decode(self.rows('baselines/chain.ndjson'))[0][1]
        changed = decode(self.rows('cases/chain/ctor-permutation.ndjson'))[0][1]
        self.assertEqual(changed['ctors'], list(reversed(original['ctors'])))
        self.assertEqual(changed['types'], original['types'])
        self.assertEqual(changed['recs'], original['recs'])
        duplicate = decode(self.rows('cases/chain/duplicate-claim.ndjson'))[0][1]
        self.assertEqual(len(duplicate['ctors']), len(original['ctors']))
        self.assertEqual(duplicate['ctors'][0], duplicate['ctors'][1])

    def test_elimination_mutations_keep_constructor_inputs(self):
        for family in suite.specifications():
            original = decode(self.rows('baselines/' + family + '.ndjson'))[0][1]
            changed = decode(self.rows('cases/' + family + '/forged-elimination.ndjson'))[0][1]
            self.assertEqual(original['types'], changed['types'])
            self.assertEqual(original['ctors'], changed['ctors'])
            self.assertNotEqual(original['recs'][0]['levelParams'], changed['recs'][0]['levelParams'])
            self.assertNotEqual(original['recs'][0]['type'], changed['recs'][0]['type'])

    def test_baseline_gates_and_declines_never_count_as_rejects(self):
        calls = []

        def no_baseline(command, path, timeout, input_mode, max_log):
            calls.append(path)
            return {'exit_code': 2, 'timed_out': False}

        report = suite.run_suite(self.manifest, HERE, ['checker'], 1, 10, execute=no_baseline)
        self.assertEqual(len(calls), 10)
        self.assertEqual(report['summary']['covered'], 0)
        self.assertEqual(report['summary']['statuses'], {'not_covered': 41})

        def decline_mutations(command, path, timeout, input_mode, max_log):
            return {'exit_code': 0 if 'baselines' in path.parts else 2, 'timed_out': False}

        report = suite.run_suite(self.manifest, HERE, ['checker'], 1, 10, execute=decline_mutations)
        self.assertEqual(report['summary']['covered'], 0)
        self.assertEqual(report['summary']['statuses'], {'declined': 41})


if __name__ == '__main__':
    unittest.main()
