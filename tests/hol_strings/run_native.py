#!/usr/bin/env python3
"""Run actual HOL checks with bounded lifetime and retained, hashed evidence."""
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

ROOT = Path(__file__).resolve().parents[2]
SMALL = {
    'validation': (['validation_tests.ml'], ['ITERATIVE_VALIDATION']),
    'reflexive': (['reflexive_tests.ml'], ['REFLEXIVE']),
    'syntax': (['string_syntax_tests.ml'], ['STRING_SYNTAX']),
    'interfaces': (['text_tests.ml'], ['TEXT_PRIMITIVE']),
    'literals': (['string_literal_tests.ml'], ['STRING_LITERAL']),
    'quotients': (['string_quotient_tests.ml'], ['STRING_QUOTIENT']),
    'structures': (['structure_major_tests.ml', 'structure_string_tests.ml'],
                   ['STRUCTURE_MAJOR', 'STRUCTURE_STRING_EXCLUSION']),
}
FULL = (
    ['tests.ml', 'nat_literal_tests.ml', 'family_tests.ml', 'indexed_tests.ml',
     'projection_core_tests.ml', 'projection_tests.ml', 'structure_tests.ml',
     'quotient_tests.ml', 'primitive_contract_tests.ml', 'text_tests.ml',
     'string_syntax_tests.ml', 'string_literal_tests.ml', 'string_quotient_tests.ml',
     'structure_major_tests.ml', 'structure_string_tests.ml', 'reflexive_tests.ml',
     'validation_tests.ml'],
    ['CORE', 'ADMISSION', 'ENVIRONMENT', 'INDUCTIVE', 'NAT_LITERAL', 'FAMILY',
     'INDEXED', 'PROJECTION_CORE', 'PROJECTION', 'STRUCTURE', 'QUOTIENT',
     'PRIMITIVE_POW_FACTORY', 'TEXT_PRIMITIVE', 'STRING_SYNTAX', 'STRING_LITERAL',
     'STRING_QUOTIENT', 'STRUCTURE_MAJOR', 'STRUCTURE_STRING_EXCLUSION', 'REFLEXIVE',
     'ITERATIVE_VALIDATION'],
)


def inventory():
    files = sorted((ROOT/'hol').glob('*.ml'))
    files += [Path(__file__).resolve(), ROOT/'scripts/toolchain-exec.sh', ROOT/'scripts/toolchain-env.sh']
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('suite', choices=[*SMALL, 'full'])
    parser.add_argument('--timeout', type=int)
    args = parser.parse_args()
    timeout = args.timeout if args.timeout is not None else (900 if args.suite == 'full' else 180)
    if not 0 < timeout <= 1800:
        parser.error('timeout must be in 1..1800 seconds')
    names, markers = FULL if args.suite == 'full' else SMALL[args.suite]
    directory = Path(tempfile.mkdtemp(prefix='hol-strings-'+args.suite+'-'))
    print(directory, flush=True)
    before = inventory()
    source = b'\n'.join((ROOT/'hol'/name).read_bytes() for name in names)
    environment = dict(os.environ, LINE_EDITOR='env')
    if args.suite == 'full':
        environment.update(HOL_PRIMITIVE_SUITE='pow', HOL_PRIMITIVE_POW_PHASE='factory')
    started = time.monotonic()
    process = subprocess.Popen(['sh', 'scripts/toolchain-exec.sh', 'hol.sh'], cwd=ROOT,
        env=environment, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, start_new_session=True)
    timed_out = False
    try:
        output, _ = process.communicate(source, timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGKILL)
        output, _ = process.communicate()
    except BaseException:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
        process.communicate()
        raise
    decoded = output.decode(errors='replace')
    found = {marker: re.findall(r'(^|\s)HOL_'+marker+r'_TESTS_PASSED (\d+)\s*$', decoded, re.M)
             for marker in markers}
    errors = bool(re.search(r'(^|\s)(Error:|Exception:)|Parse error|Error in included file', decoded))
    after = inventory()
    passed = (process.returncode == 0 and not timed_out and not errors and before == after
              and all(len(matches) == 1 for matches in found.values()))
    report = {'suite': args.suite, 'passed': passed, 'exit': process.returncode,
        'timed_out': timed_out, 'timeout_seconds': timeout, 'errors_detected': errors,
        'elapsed_seconds': time.monotonic()-started, 'markers': found,
        'sources_before': before, 'sources_after': after,
        'log_sha256': hashlib.sha256(output).hexdigest()}
    (directory/'hol.log').write_bytes(output)
    (directory/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if not k.startswith('sources_')}, indent=2))
    if not passed:
        print(decoded[-16000:])
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())
