#!/usr/bin/env python3
"""Bounded native HOL primitive-contract regression phases."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import time

ROOT=Path(__file__).resolve().parents[2]
PHASES={
    'pow': ('factory','body','base','step','order','dependencies','poison','replay','missing'),
    'shift-left': ('factory','body','named','base','step','order','output','replay','missing',
                   'checks','equations'),
    'admission': ('all',),
}

def inventory():
    files=[*sorted((ROOT/'hol').glob('*.ml')),Path(__file__).resolve(),
        ROOT/'scripts/toolchain-exec.sh',ROOT/'scripts/toolchain-env.sh']
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation',choices=PHASES)
    parser.add_argument('--phase')
    parser.add_argument('--timeout',type=int,default=180)
    args=parser.parse_args()
    phase=args.phase or PHASES[args.operation][0]
    if phase not in PHASES[args.operation]:
        parser.error('phase must be one of '+', '.join(PHASES[args.operation]))
    if not 0<args.timeout<=900:
        parser.error('timeout must be in 1..900 seconds')
    operation=args.operation.upper().replace('-','_')
    env=dict(os.environ,LINE_EDITOR='env',HOL_PRIMITIVE_SUITE=args.operation)
    env['HOL_PRIMITIVE_'+operation+'_PHASE']=phase
    name='primitive_contract_tests.ml'
    marker='HOL_PRIMITIVE_'+operation+'_'+phase.upper()+'_TESTS_PASSED'
    if args.operation=='admission':
        name='primitive_admission_tests.ml'
        marker='HOL_PRIMITIVE_ADMISSION_TESTS_PASSED'
    out=Path(tempfile.mkdtemp(prefix='hol-primitive-'+args.operation+'-'+phase+'-'))
    print(out,flush=True)
    before=inventory()
    source=(ROOT/'hol'/name).read_bytes()
    start=time.monotonic()
    p=subprocess.Popen(['sh','scripts/toolchain-exec.sh','hol.sh'],cwd=ROOT,
        env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
        start_new_session=True)
    timed_out=False
    try:
        output,_=p.communicate(source,timeout=args.timeout)
    except subprocess.TimeoutExpired:
        timed_out=True
        os.killpg(p.pid,signal.SIGKILL)
        output,_=p.communicate()
    except BaseException:
        if p.poll() is None:
            os.killpg(p.pid,signal.SIGKILL)
        p.communicate()
        raise
    decoded=output.decode(errors='replace')
    matches=re.findall(r'(^|\s)'+marker+r' (\d+)\s*$',decoded,re.M)
    errors=bool(re.search(r'(^|\s)(Error:|Exception:)|Parse error|Error in included file',decoded))
    after=inventory()
    passed=p.returncode==0 and not timed_out and not errors and len(matches)==1 and before==after
    report=dict(operation=args.operation,phase=phase,passed=passed,exit=p.returncode,
        timed_out=timed_out,errors_detected=errors,timeout_seconds=args.timeout,
        elapsed_seconds=time.monotonic()-start,marker=marker,matches=matches,
        sources_before=before,sources_after=after,log_sha256=hashlib.sha256(output).hexdigest())
    (out/'hol.log').write_bytes(output)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if not k.startswith('sources_')},indent=2))
    if not passed:
        print(decoded[-12000:])
    return 0 if passed else 1

if __name__=='__main__':
    raise SystemExit(main())
