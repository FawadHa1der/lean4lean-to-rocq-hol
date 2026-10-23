"""Bounded export-path tests for native text certificates; no verdict oracle."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time
import tempfile

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT
spec = importlib.util.spec_from_file_location('string_builder', PROJECT/'tests/hol_indexed_audit/witnesses.py')
builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)
V, S, C, A, bind = builder.V, builder.S, builder.C, builder.A, builder.bind
ZERO, ONE = builder.ZERO, builder.ONE


class Wire(builder.Wire):
    def expr(self, term, context=()):
        if term[0] == 'strlit':
            return self.raw({'strVal': term[1]})
        if term[0] == 'natlit':
            return self.raw({'natVal': str(term[1])})
        return super().expr(term, context)


def fixture():
    seed = PROJECT/'arena/corpus/tutorial/102_aNatLit.ndjson'
    wire = Wire(builder.admission_only(builder.rows_of(seed.read_bytes())))
    nat, char, text = C('Nat'), C('Char'), C('String')
    universe = ('param', 'u')
    at = S(('succ', universe))
    li = lambda e: A(C('List', [universe]), e)
    lc = A(C('List', [ZERO]), char)
    pi = lambda ps, body: bind('forallE', ps, body)
    lam = lambda ps, body: bind('lam', ps, body)
    zero = ('natlit', 0)
    wire.definition('Char', [], S(ONE), nat)
    wire.definition('String', [], S(ONE), nat)
    wire.definition('List', ['u'], pi([('a', at)], S(ONE)), lam([('a', at)], nat))
    wire.definition('List.nil', ['u'], pi([('a', at)], li(V('a'))), lam([('a', at)], zero))
    cons = [('a', at), ('x', V('a')), ('tail', li(V('a')))]
    wire.definition('List.cons', ['u'], pi(cons, li(V('a'))), lam(cons, V('tail')))
    wire.definition('Char.ofNat', [], pi([('x', nat)], char), lam([('x', nat)], zero))
    wire.definition('String.ofList', [], pi([('xs', lc)], text), lam([('xs', lc)], zero))
    return wire


def name_index(wire, name):
    return wire.name(name)


def declaration(wire, name):
    idx = name_index(wire, name)
    return next(d['def'] for d in wire.decls if 'def' in d and d['def']['name'] == idx)


def literal(wire, value, name='LiteralResult'):
    wire.definition(name, [], C('String'), ('strlit', value))


def comparison(wire, a, b):
    p = ('P', bind('forallE', [('s', C('String'))], S(ONE)))
    args = [p, ('x', A(V('P'), ('strlit', a)))]
    wire.definition('Compare', [], bind('forallE', args, A(V('P'), ('strlit', b))),
                    bind('lam', args, V('x')))


def cases():
    out = []
    def put(label, wire, expected):
        out.append((label, wire.finish(), expected))
    w = fixture()
    put('interfaces', w, 0)
    for label, value in [('empty', ''), ('nul', '\x00'), ('ascii', 'abc'),
                         ('unicode', '\u00e9\u0301\U0010ffff')]:
        w = fixture(); literal(w, value); put(label, w, 0)
    w = fixture(); comparison(w, 'a', 'a'); put('same-literal', w, 0)
    w = fixture(); comparison(w, 'a', 'b'); put('different-literal', w, 2)
    w = fixture(); comparison(w, '\u00e9', 'e\u0301'); put('no-normalization', w, 2)
    w = fixture(); literal(w, 'abc'); w.decls.reverse(); put('reverse-dependencies', w, 0)
    for name in ('Char.ofNat', 'String.ofList'):
        for safety in ('unsafe', 'partial'):
            w = fixture(); literal(w, 'a'); declaration(w, name)['safety'] = safety
            put(name+'-'+safety, w, 2)
        w = fixture(); literal(w, 'a'); idx = w.name(name)
        w.decls = [d for d in w.decls if d.get('def', {}).get('name') != idx]
        put(name+'-missing', w, 2)
        w = fixture(); literal(w, 'a'); declaration(w, name)['value'] = w.expr(S(ZERO))
        put(name+'-bad-body', w, 2)
        w = fixture(); literal(w, 'a'); declaration(w, name)['levelParams'] = [w.name('unused')]
        put(name+'-universe', w, 2)
    w = fixture(); literal(w, 'a'); declaration(w, 'List.nil')['levelParams'] = []
    put('nil-universe-arity', w, 2)
    w = fixture(); literal(w, 'a'); declaration(w, 'List.cons')['levelParams'] = []
    put('cons-universe-arity', w, 2)
    w = fixture(); literal(w, 'a'); declaration(w, 'LiteralResult')['type'] = w.expr(S(ZERO))
    put('literal-not-proof', w, 2)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--socket', required=True)
    args = parser.parse_args()
    directory = Path(tempfile.mkdtemp(prefix='hol-string-exports-'))
    print(directory, flush=True)
    tracked = [Path(__file__).resolve(), PROJECT/'tests/hol_indexed_audit/witnesses.py',
        PROJECT/'scripts/test_metadata_mutations.py', PROJECT/'scripts/test_arena.py',
        PROJECT/'arena/corpus/tutorial/102_aNatLit.ndjson']
    def inventory():
        return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in tracked}
    before = inventory()
    results = []
    all_cases = cases()
    for label, rows, expected in all_cases:
        path = directory/(label+'.ndjson')
        data = b''.join((json.dumps(row, ensure_ascii=True, separators=(',', ':'))+'\n').encode() for row in rows)
        path.write_bytes(data)
        started = time.monotonic()
        try:
            process = subprocess.run([sys.executable, str(ROOT/'scripts/hol-check.py'),
                '--socket', args.socket, '--timeout', '45', str(path)], cwd=ROOT,
                capture_output=True, timeout=55)
            code, output = process.returncode, (process.stdout+process.stderr).decode(errors='replace')
        except subprocess.TimeoutExpired as error:
            code, output = None, str(error)
        result = {'name':label, 'expected':expected, 'exit':code, 'passed':code==expected,
            'elapsed':time.monotonic()-started, 'sha256':hashlib.sha256(data).hexdigest(), 'output':output}
        results.append(result)
        print(label, code, expected, flush=True)
        if label == 'interfaces' and code != expected:
            break
    after = inventory()
    inputs_stable = all(hashlib.sha256((directory/(r['name']+'.ndjson')).read_bytes()).hexdigest()
                        == r['sha256'] for r in results)
    report = {'passed':len(results)==len(all_cases) and all(r['passed'] for r in results)
              and before==after and inputs_stable, 'results':results,
              'expected_count':len(all_cases), 'executed_count':len(results),
              'sources_before':before, 'sources_after':after, 'inputs_stable':inputs_stable}
    (directory/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    sys.exit(0 if report['passed'] else 1)


if __name__ == '__main__':
    main()
