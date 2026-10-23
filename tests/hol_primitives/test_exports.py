"""General frontend tests for symbolic shiftLeft admission and computation."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('primitive_wire',ROOT/'tests/hol_indexed_audit/witnesses.py')
builder=importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)
V,S,C,A,bind=builder.V,builder.S,builder.C,builder.A,builder.bind
ONE=builder.ONE

def fixture():
    seed=ROOT/'arena/corpus/tutorial/102_aNatLit.ndjson'
    wire=builder.Wire(builder.admission_only(builder.rows_of(seed.read_bytes())))
    nat=C('Nat')
    zero=C('Nat.zero')
    succ=lambda e:A(C('Nat.succ'),e)
    lam=lambda args,body:bind('lam',args,body)
    pi=lambda args,body:bind('forallE',args,body)
    unary=pi([('argument',nat)],nat)
    binary=pi([('x',nat),('y',nat)],nat)
    motive=lam([('index',nat)],nat)
    add=lam([('x',nat),('y',nat)],A(C('Nat.rec',[ONE]),motive,V('x'),
        lam([('k',nat),('ih',nat)],succ(V('ih'))),V('y')))
    mul=lam([('x',nat),('y',nat)],A(C('Nat.rec',[ONE]),motive,zero,
        lam([('k',nat),('ih',nat)],A(C('Nat.add'),V('ih'),V('x'))),V('y')))
    two=succ(succ(zero))
    step=lam([('k',nat),('ih',unary),('v',nat)],
        A(V('ih'),A(C('Nat.mul'),two,V('v'))))
    shift=lam([('x',nat),('y',nat)],A(C('Nat.rec',[ONE]),
        lam([('index',nat)],unary),lam([('v',nat)],V('v')),step,V('y'),V('x')))
    for name,body in [('Nat.add',add),('Nat.mul',mul),('Nat.shiftLeft',shift)]:
        wire.definition(name,[],binary,body)
    return wire

def cases():
    w=fixture()
    yield 'admission-gate',w.finish(),0
    nat=C('Nat')
    zero=C('Nat.zero')
    succ=lambda e:A(C('Nat.succ'),e)
    one=succ(zero)
    result=A(C('Nat.shiftLeft'),one,one)
    for label,expected,code in [('compute-one',succ(one),0),('wrong-result',succ(succ(one)),2)]:
        w=fixture()
        parameters=[('P',bind('forallE',[('n',nat)],S(ONE))),('witness',A(V('P'),result))]
        w.definition('CheckShift',[],bind('forallE',parameters,A(V('P'),expected)),
            bind('lam',parameters,V('witness')))
        yield label,w.finish(),code

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--socket',required=True)
    parser.add_argument('--timeout',type=int,default=180)
    args=parser.parse_args()
    if not 0<args.timeout<=600:
        parser.error('timeout must be in 1..600 seconds')
    out=Path(tempfile.mkdtemp(prefix='hol-shift-left-exports-'))
    print(out,flush=True)
    sources=[Path(__file__).resolve(),ROOT/'tests/hol_indexed_audit/witnesses.py',
        ROOT/'scripts/test_metadata_mutations.py',ROOT/'scripts/test_arena.py',
        ROOT/'arena/corpus/tutorial/102_aNatLit.ndjson']
    def inventory():
        return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    before=inventory()
    results=[]
    for label,rows,expected in cases():
        data=b''.join((json.dumps(row,separators=(',',':'))+'\n').encode() for row in rows)
        path=out/(label+'.ndjson')
        path.write_bytes(data)
        start=time.monotonic()
        try:
            p=subprocess.run([sys.executable,str(ROOT/'scripts/hol-check.py'),'--socket',args.socket,
                '--timeout',str(args.timeout),str(path)],cwd=ROOT,capture_output=True,
                timeout=args.timeout+10)
            code,output=p.returncode,(p.stdout+p.stderr).decode(errors='replace')
        except subprocess.TimeoutExpired as ex:
            code,output=None,str(ex)
        timed_out='timeout' in output.lower()
        result=dict(name=label,expected=expected,exit=code,output=output,timed_out=timed_out,
            elapsed=time.monotonic()-start,sha256=hashlib.sha256(data).hexdigest(),
            passed=code==expected and not timed_out)
        results.append(result)
        print(json.dumps(result),flush=True)
        if label=='admission-gate' and not result['passed']:
            break
    after=inventory()
    inputs_stable=all(hashlib.sha256((out/(r['name']+'.ndjson')).read_bytes()).hexdigest()==r['sha256']
        for r in results)
    report=dict(passed=len(results)==3 and all(r['passed'] for r in results) and before==after
        and inputs_stable,results=results,sources_before=before,sources_after=after,
        inputs_stable=inputs_stable)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return 0 if report['passed'] else 1

if __name__=='__main__':
    raise SystemExit(main())
