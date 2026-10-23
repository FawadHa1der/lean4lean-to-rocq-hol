#!/usr/bin/env python3
"""Bounded syntax-construction differential tests; never a verdict oracle."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('phase', choices=['quotation', 'bridge'])
args = parser.parse_args()
here = Path(__file__).resolve().parent
root = here.parents[1]
driver = root/'scripts/toolchain-exec.sh'
output_dir = Path(tempfile.mkdtemp(prefix='hol-syntax-cache-'))
paths = sorted((root/'hol').glob('*.ml')) + [here/'quotation_tests.ml', here/'bridge_tests.ml', Path(__file__).resolve()]
if args.phase == 'bridge':
    paths += [root/'frontend/hol_check.ml'] + [root/'build/frontend'/f'{n}.{e}'
              for n in ('wire','replay','hol_input') for e in ('cmo','cmi')]
def inventory():
    return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
before = inventory()
source = 'use_file_raise_failure := true;;\nload_path := [Sys.getcwd()];;\n'
if args.phase == 'bridge':
    for package in ('zarith','yojson'):
        path = subprocess.check_output(['sh',str(driver),'ocamlfind','query',package],text=True).strip()
        source += 'Topdirs.dir_directory '+json.dumps(path)+';;\n'
    source += 'Topdirs.dir_directory '+json.dumps(str(root/'build/frontend'))+';;\n'
    source += '#load "unix.cma";;\n#load "zarith.cma";;\n#load "yojson.cma";;\n'
    for name in ('wire','replay','hol_input'):
        source += 'Topdirs.dir_load Format.std_formatter '+json.dumps(str(root/'build/frontend'/f'{name}.cmo'))+';;\n'
    source += 'needs "hol/environment.ml";;\nneeds "hol/primitive_validation.ml";;\nunset_jrh_lexer;;\nneeds "frontend/hol_check.ml";;\n'
source += 'needs '+json.dumps(str(here/(args.phase+'_tests.ml')))+';;\n'
started = time.monotonic()
p = subprocess.Popen(['sh',str(driver),'hol.sh'],cwd=root,env=dict(os.environ,LINE_EDITOR='env'),
    stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
timed_out = False
try:
    output,_ = p.communicate(source.encode(),timeout=180)
except subprocess.TimeoutExpired:
    timed_out = True
    os.killpg(p.pid,signal.SIGKILL)
    output,_ = p.communicate()
except BaseException:
    if p.poll() is None:
        os.killpg(p.pid,signal.SIGKILL)
    p.communicate()
    raise
text = output.decode(errors='replace')
kind = 'QUOTE' if args.phase=='quotation' else 'BRIDGE'
markers = re.findall(r'^HOL_'+kind+r'_CACHE_TESTS_PASSED (\d+)\s*$',text,re.M)
benchmarks = re.findall(r'^HOL_'+kind+r'_BENCH .+$',text,re.M)
errors = bool(re.search(r'(^|\s)(Error:|Exception:)|Parse error|Error in included file',text))
after = inventory()
passed = p.returncode==0 and not timed_out and not errors and before==after and len(markers)==1 and len(benchmarks)==7
log = output_dir/'run.log'
log.write_bytes(output)
report = {'phase':args.phase,'passed':passed,'exit':p.returncode,'timed_out':timed_out,
    'elapsed_seconds':time.monotonic()-started,'assertions':markers,'benchmarks':benchmarks,
    'sources_before':before,'sources_after':after,'log_sha256':hashlib.sha256(output).hexdigest()}
(output_dir/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if not k.startswith('sources_')},indent=2))
print('Evidence:',output_dir)
if not passed:
    print(text[-12000:])
sys.exit(0 if passed else 1)
