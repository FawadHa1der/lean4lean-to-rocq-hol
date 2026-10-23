import hashlib
import importlib.util
import json
import os
from pathlib import Path
import selectors
import subprocess
import sys
import time

base = Path(__file__).resolve().parent
root = base / 'rb-probe'
fixture_root = Path('/Users/fawadhaider/code/lean4 in rocq:hol light/tests/hol_indexed_audit/p2_fix/diagnostics')
environment = dict(os.environ, LINE_EDITOR='env', P2_FIXTURES=str(fixture_root))
environment.pop('HOL_ML_PATH', None)
for package in ('zarith', 'yojson'):
    environment['P2_' + package.upper()] = subprocess.check_output(
        ['ocamlfind', 'query', package], text=True).strip()
bootstrap = b'''Topdirs.dir_directory (Sys.getenv "P2_ZARITH");;
Topdirs.dir_directory (Sys.getenv "P2_YOJSON");;
Topdirs.dir_directory "build/frontend";;
#load "unix.cma";;
#load "zarith.cma";;
#load "yojson.cma";;
Topdirs.dir_load Format.std_formatter "build/frontend/wire.cmo";;
Topdirs.dir_load Format.std_formatter "build/frontend/replay.cmo";;
Topdirs.dir_load Format.std_formatter "build/frontend/hol_input.cmo";;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
let () = try needs "hol/environment.ml" with exn -> prerr_endline(Printexc.to_string exn); exit 3;;
unset_jrh_lexer;;
let () = try needs "frontend/hol_check.ml" with exn -> prerr_endline(Printexc.to_string exn); exit 3;;
let () = List.iter (fun label ->
  Printf.printf "RB_CASE %s\\n%!" label;
  let file=Filename.concat (Sys.getenv "P2_FIXTURES") (label^".ndjson") in
  let code,message=Hol_check.check_file file in
  Printf.printf "RB_VERDICT %s %d %s\\n%!" label code message)
  ["071_rbTreeRef";"082_RBTree.id_spec"];;
print_endline "RB_PROBE_COMPLETE";;
exit 0;;
'''
spec = importlib.util.spec_from_file_location('private_runner', root / 'scripts/hol-check.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
before = runner.project_snapshot(root)
inputs = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
          for folder in ('hol', 'frontend', 'build/frontend') for p in (root / folder).glob('*') if p.is_file()}
start = time.monotonic()
process = subprocess.Popen(['hol.sh'], cwd=root, env=environment, stdin=subprocess.PIPE,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
tail = bytearray()
try:
    process.stdin.write(bootstrap)
    process.stdin.close()
    with selectors.DefaultSelector() as selector:
        selector.register(process.stdout, selectors.EVENT_READ)
        while process.poll() is None or selector.get_map():
            if time.monotonic() - start > 180:
                raise TimeoutError('bounded private diagnostic exceeded 180 seconds')
            for key, _ in selector.select(0.2):
                chunk = os.read(key.fileobj.fileno(), 65536)
                if not chunk:
                    selector.unregister(key.fileobj)
                else:
                    tail.extend(chunk)
                    if len(tail) > 2 * 1024 * 1024:
                        del tail[:-2 * 1024 * 1024]
    code = process.wait()
finally:
    if process.poll() is None:
        os.killpg(process.pid, 9)
        process.wait()
    (base / 'rb-probe.log').write_bytes(tail)
if any(hashlib.sha256((root / p).read_bytes()).hexdigest() != digest for p, digest in inputs.items()):
    raise ValueError('private source changed during diagnostic')
after = runner.project_snapshot(root)
runner.require_stable_startup(before, after)
summary = {'exit_code': code, 'seconds': time.monotonic() - start, 'inputs': inputs,
           'project_snapshot_before': before, 'project_snapshot_after': after,
           'bootstrap_sha256': hashlib.sha256(bootstrap).hexdigest(),
           'kind': 'private-direct-HOL-probe-not-server-readiness', 'unchanged': before == after,
           'scope': 'Project files and supplied bootstrap only; no runtime/toolchain/semantics attestation.',
           'log_sha256': hashlib.sha256(tail).hexdigest(), 'log_bytes': len(tail)}
(base / 'rb-probe.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
for line in tail.decode(errors='replace').splitlines():
    if line.startswith('RB_') or 'Error:' in line or 'Exception:' in line:
        print(line)
sys.exit(code)
