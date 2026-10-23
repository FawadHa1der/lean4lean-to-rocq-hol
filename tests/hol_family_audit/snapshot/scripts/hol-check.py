#!/usr/bin/env python3
# Copyright (c) 2026 Fawad Haider. All rights reserved.
"""Private, fork-isolated HOL Light runner and Arena-compatible client."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import secrets
import selectors
import signal
import socket
import stat
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
MAX_FRAME = 32768
MAX_REQUEST = 16384
LOG_LIMIT = 65536
MAX_PROVENANCE = 1024 * 1024
MAX_INPUT_BYTES = 32 * 1024 * 1024
MAX_SOURCE_BYTES = 2 * 1024 * 1024
MAX_INPUT_TOTAL = 128 * 1024 * 1024
MAX_INPUT_FILES = 512
SOURCE_ROOTS = ('hol/environment.ml', 'frontend/hol_check.ml', 'frontend/hol_server.ml')
BOOT_FILES = {
    'scripts/hol-check.py': 'supervisor-source',
    'scripts/hol-server.sh': 'launcher-source',
    'scripts/toolchain-exec.sh': 'launcher-source',
    'scripts/toolchain-env.sh': 'launcher-source',
    **{f'build/frontend/{name}.{ext}': 'bridge-' + role
       for name in ('wire', 'replay', 'hol_input')
       for ext, role in (('cmo', 'bytecode'), ('cmi', 'interface'))},
}
BOOTSTRAP = b'''Topdirs.dir_directory (Sys.getenv "HOL_RUNNER_ZARITH");;
Topdirs.dir_directory (Sys.getenv "HOL_RUNNER_YOJSON");;
Topdirs.dir_directory "build/frontend";;
#load "unix.cma";;
#load "zarith.cma";;
#load "yojson.cma";;
Topdirs.dir_load Format.std_formatter (Filename.concat (Sys.getenv "HOL_RUNNER_ROOT") "build/frontend/wire.cmo");;
Topdirs.dir_load Format.std_formatter (Filename.concat (Sys.getenv "HOL_RUNNER_ROOT") "build/frontend/replay.cmo");;
Topdirs.dir_load Format.std_formatter (Filename.concat (Sys.getenv "HOL_RUNNER_ROOT") "build/frontend/hol_input.cmo");;
use_file_raise_failure := true;;
load_path := [Sys.getcwd()];;
let () = try needs "hol/environment.ml"
with exn -> prerr_endline (Printexc.to_string exn); exit 3;;
unset_jrh_lexer;;
let () = try
  needs "frontend/hol_check.ml";
  needs "frontend/hol_server.ml"
with exn -> prerr_endline (Printexc.to_string exn); exit 3;;
exit 3;;
'''
HOL_ERROR = re.compile(
    rb'(^|[\r\n]|# )[ \t]*(?:Error:|Exception:|Parse error|Fatal error:)|'
    rb'Error in included file|Cannot find file|HOL_RUNNER_FAULT:', re.MULTILINE)


class Parser(argparse.ArgumentParser):
    def error(self, message):
        raise ValueError(message)


def positive_seconds(value):
    number = float(value)
    if not math.isfinite(number) or not 0 < number <= 86400:
        raise ValueError('timeout must be finite and in (0, 86400] seconds')
    return number


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON field')
        result[key] = value
    return result


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, ensure_ascii=True,
                       separators=(',', ':')) + '\n').encode('ascii')


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def file_identity(info):
    return {key: getattr(info, 'st_' + key)
            for key in ('dev', 'ino', 'mode', 'uid', 'size', 'mtime_ns', 'ctime_ns')}


def read_project_input(root, relative, role):
    path = root / relative
    # Do not follow redirected project sources or block on a special file.
    for parent in path.relative_to(root).parents:
        if (root / parent).is_symlink():
            raise ValueError(f'symlinked provenance input directory: {relative}')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, 'rb') as stream:
        before = os.fstat(stream.fileno())
        if not stat.S_ISREG(before.st_mode) or before.st_size > MAX_INPUT_BYTES:
            raise ValueError(f'nonregular or oversized provenance input: {relative}')
        data = stream.read(MAX_INPUT_BYTES + 1)
        after = os.fstat(stream.fileno())
    if (len(data) > MAX_INPUT_BYTES or file_identity(before) != file_identity(after)
            or file_identity(after) != file_identity(os.lstat(path))):
        raise ValueError(f'provenance input changed while hashing: {relative}')
    return data, {'path': relative, 'role': role, 'sha256': sha256(data),
                  'size_bytes': len(data), 'identity': file_identity(after)}


def source_tokens(source):
    """Small lexical scanner, not an OCaml evaluator or general dependency analyzer."""
    at, size = 0, len(source)
    raw_pattern = re.compile(r'\{([a-z_]*)\|')
    char_pattern = re.compile(r"'(?:[^'\\\r\n]|\\(?:[0-9]{3}|x[0-9a-fA-F]{2}|.))'")
    word_pattern = re.compile(r"[A-Za-z_][A-Za-z_0-9']*")

    def quoted_end(start, delimiter):
        pos = start + 1
        while pos < size:
            if source[pos] == '\\':
                pos += 2
            elif source[pos] == delimiter:
                return pos + 1
            else:
                pos += 1
        raise ValueError('unterminated source quotation in dependency scan')

    while at < size:
        if source[at].isspace():
            at += 1
        elif source.startswith('(*', at):
            depth, at = 1, at + 2
            while at < size and depth:
                if source.startswith('(*', at):
                    depth, at = depth + 1, at + 2
                elif source.startswith('*)', at):
                    depth, at = depth - 1, at + 2
                elif source[at] == '"':
                    at = quoted_end(at, '"')
                else:
                    at += 1
            if depth:
                raise ValueError('unterminated comment in dependency scan')
        elif source[at] in ('"', '`'):
            end = quoted_end(at, source[at])
            yield ('string' if source[at] == '"' else 'quotation', source[at + 1:end - 1])
            at = end
        else:
            raw = raw_pattern.match(source, at)
            char = char_pattern.match(source, at)
            word = word_pattern.match(source, at)
            if raw:
                end = source.find('|' + raw.group(1) + '}', raw.end())
                if end < 0:
                    raise ValueError('unterminated quoted string in dependency scan')
                yield ('quotation', '')
                at = end + len(raw.group(1)) + 2
            elif char:
                yield ('quotation', '')
                at = char.end()
            elif word:
                yield ('identifier', word.group())
                at = word.end()
            else:
                yield ('punctuation', source[at])
                at += 1


def literal_needs(data):
    if len(data) > MAX_SOURCE_BYTES:
        raise ValueError('source exceeds dependency scan byte limit')
    tokens = list(source_tokens(data.decode('utf-8')))
    dependencies = set()
    unsupported = {'loadt', 'loadf', 'loads', 'load_on_path', 'load_file', 'use_file',
                   'use_silently', 'use_output', 'dir_load', 'dir_use', 'dir_mod_use',
                   'load_path', 'hol_dir', 'Dynlink'}
    for index, (kind, value) in enumerate(tokens):
        if kind != 'identifier':
            continue
        previous = tokens[index - 1] if index else None
        if value in unsupported or (previous == ('punctuation', '#')
                                    and value in ('use', 'mod_use', 'load', 'directory')):
            raise ValueError(f'unsupported project loader form in dependency scan: {value}')
        if value != 'needs':
            continue
        following = tokens[index + 1] if index + 1 < len(tokens) else None
        if (previous == ('punctuation', '.') or following is None
                or following[0] != 'string'
                or not re.fullmatch(r'(?:hol|frontend)/(?:[A-Za-z0-9_-]+/)*[A-Za-z0-9_-]+\.ml',
                                    following[1])):
            raise ValueError('needs must use a literal canonical project .ml path')
        dependencies.add(following[1])
    return sorted(dependencies)


def project_snapshot(root):
    root = root.resolve(strict=True)
    inputs, edges = {}, {}
    pending = list(SOURCE_ROOTS)
    total = 0

    def add(relative, role):
        nonlocal total
        if len(inputs) >= MAX_INPUT_FILES:
            raise ValueError('too many project provenance inputs')
        data, entry = read_project_input(root, relative, role)
        total += len(data)
        if total > MAX_INPUT_TOTAL:
            raise ValueError('project provenance inputs exceed total byte limit')
        inputs[relative] = entry
        return data

    while pending:
        relative = pending.pop()
        if relative in inputs:
            continue
        dependencies = literal_needs(add(relative, 'hol-source-dependency'))
        edges[relative] = dependencies
        pending.extend(dependencies)
    for relative, role in sorted(BOOT_FILES.items()):
        add(relative, role)
    return {'project_root': str(root), 'source_roots': list(SOURCE_ROOTS),
            'literal_needs': edges, 'inputs': [inputs[key] for key in sorted(inputs)],
            'bootstrap': {'sha256': sha256(BOOTSTRAP), 'size_bytes': len(BOOTSTRAP)}}


def require_stable_startup(before, after):
    if before != after:
        old = {item['path']: item for item in before['inputs']}
        new = {item['path']: item for item in after['inputs']}
        changed = sorted(path for path in old.keys() | new.keys() if old.get(path) != new.get(path))
        raise ValueError('startup provenance changed before READY: ' + ', '.join(changed[:8]))


def output_location(path):
    path = Path(os.path.abspath(path))
    if os.path.lexists(path):
        raise ValueError('provenance output already exists; refusing to overwrite')
    # Pin the immediate directory with a descriptor during publication; no final symlink.
    descriptor = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    return path, descriptor


def atomic_private_output(path, data):
    if len(data) > MAX_PROVENANCE:
        raise ValueError('provenance manifest exceeds byte limit')
    path, parent = output_location(path)
    temporary = '.hol-provenance-' + secrets.token_hex(16)
    created = False
    try:
        fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                     0o600, dir_fd=parent)
        created = True
        with os.fdopen(fd, 'wb') as stream:
            os.fchmod(stream.fileno(), 0o600)
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        # Hard-link publication is atomic and fails if any destination already exists.
        os.link(temporary, path.name, src_dir_fd=parent, dst_dir_fd=parent,
                follow_symlinks=False)
        os.unlink(temporary, dir_fd=parent)
        created = False
        os.fsync(parent)
    finally:
        if created:
            os.unlink(temporary, dir_fd=parent)
        os.close(parent)
    verify_private_output(path, sha256(data))


def verify_private_output(path, expected_sha256):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, 'rb') as stream:
        info = os.fstat(stream.fileno())
        if (not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid()
                or stat.S_IMODE(info.st_mode) != 0o600 or info.st_nlink != 1
                or info.st_size > MAX_PROVENANCE):
            raise ValueError('provenance output must be a private bounded regular file')
        data = stream.read(MAX_PROVENANCE + 1)
        if (file_identity(info) != file_identity(os.fstat(stream.fileno()))
                or file_identity(info) != file_identity(os.lstat(path))
                or len(data) > MAX_PROVENANCE or sha256(data) != expected_sha256):
            raise ValueError('provenance output integrity mismatch')


def publish_provenance(root, before, directory, endpoint, hol_pid, args, started_at):
    info = os.lstat(directory)
    if (not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid()
            or stat.S_IMODE(info.st_mode) != 0o700):
        raise ValueError('provenance run directory must be private mode 0700')
    after = project_snapshot(root)
    require_stable_startup(before, after)
    manifest = {
        'version': 1, 'kind': 'hol-runner-startup-provenance', 'scope': 'project-inputs-only',
        'limitations': [
            'Two matching filesystem snapshots, not an attestation of executed bytes or runtime state.',
            'No HOL toolchain, external OCaml libraries, dynamic libraries, OS, or semantic attestation.',
            'Literal-needs closure under the project loader contract; not analysis of arbitrary OCaml.',
            'Bytecode and interfaces are hashed; correspondence to build sources is not established.',
            'Edits after READY and transient changes restored between observations may go undetected.',
        ],
        'startup': {'started_at': started_at, 'ready_at': utc_now(),
                    'supervisor_pid': os.getpid(), 'hol_pid': hol_pid, 'socket': endpoint,
                    'case_timeout_seconds': args.case_timeout,
                    'before_snapshot_sha256': sha256(json_bytes(before)),
                    'ready_snapshot_sha256': sha256(json_bytes(after)),
                    'comparison': 'before-launch-and-at-ready-identical'},
        'snapshot_sha256': sha256(json_bytes(before)), 'snapshot': before,
    }
    data = json_bytes(manifest)
    path = Path(directory) / 'provenance.json'
    atomic_private_output(path, data)
    if args.provenance_output:
        atomic_private_output(args.provenance_output, data)
    return {'provenance_path': str(path), 'provenance_sha256': sha256(data),
            **({'provenance_output': os.path.abspath(args.provenance_output)}
               if args.provenance_output else {})}


def private_socket(path):
    if not os.path.isabs(path) or len(os.fsencode(path)) >= 100:
        raise ValueError('socket must be an absolute path shorter than 100 bytes')
    directory = os.lstat(os.path.dirname(path))
    endpoint = os.lstat(path)
    if (not stat.S_ISDIR(directory.st_mode) or directory.st_uid != os.getuid()
            or stat.S_IMODE(directory.st_mode) != 0o700):
        raise ValueError('socket directory must be owned by this user with mode 0700')
    if (not stat.S_ISSOCK(endpoint.st_mode) or endpoint.st_uid != os.getuid()
            or stat.S_IMODE(endpoint.st_mode) != 0o600):
        raise ValueError('socket must be owned by this user with mode 0600')


def diagnostic(message):
    # Keep terminal controls and arbitrary source bytes out of diagnostics.
    return ''.join(ch if ch.isprintable() else ' ' for ch in message[:4096])


def client(argv):
    parser = Parser(description='Check one file using an already initialized HOL runner.')
    parser.add_argument('--socket', required=True, help='private Unix socket from hol-server.sh')
    parser.add_argument('--timeout', default=30, type=positive_seconds,
                        help='requested case wall limit (seconds; default: 30)')
    parser.add_argument('--transport-grace', default=5, type=positive_seconds,
                        help='additional IPC deadline allowance (seconds; default: 5)')
    parser.add_argument('file', help='input file, appended by scripts/test_arena.py')
    args = parser.parse_args(argv)
    private_socket(args.socket)
    if args.file == '-' or '\0' in args.file:
        raise ValueError('a real file path is required; stdin is not supported')
    request = json.dumps({'version': 1, 'path': os.path.abspath(args.file),
                          'timeout_seconds': args.timeout}, ensure_ascii=True).encode() + b'\n'
    if len(request) > MAX_REQUEST:
        raise ValueError('request path exceeds the protocol size limit')
    deadline = time.monotonic() + args.timeout + args.transport_grace
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as connection:
        connection.settimeout(max(0.001, deadline - time.monotonic()))
        connection.connect(args.socket)
        connection.sendall(request)
        data = bytearray()
        while not data.endswith(b'\n'):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError('transport deadline exceeded; no checker verdict received')
            connection.settimeout(remaining)
            chunk = connection.recv(min(4096, MAX_FRAME + 1 - len(data)))
            if not chunk:
                raise ValueError('server closed before a complete response')
            data.extend(chunk)
            if len(data) > MAX_FRAME or b'\n' in data[:-1]:
                raise ValueError('oversized or multiple response frames')
    result = json.loads(data, object_pairs_hook=unique_object)
    if (not isinstance(result, dict) or type(result.get('version')) is not int
            or result['version'] != 1 or type(result.get('code')) is not int
            or result['code'] not in (0, 1, 2, 3)
            or not isinstance(result.get('message'), str)
            or result.get('kind') not in ('result', 'timeout', 'fault')
            or (result['kind'] == 'timeout' and result['code'] != 2)
            or (result['kind'] == 'fault' and result['code'] != 3)):
        raise ValueError('invalid server response')
    labels = ('accept', 'reject', 'decline', 'fault')
    print(f"HOL {labels[result['code']]}: {diagnostic(result['message'])}", file=sys.stderr)
    return result['code']


def stop_process(process, hol_pid):
    # The HOL parent handles TERM by killing and waiting for its active child.
    try:
        if hol_pid is None:
            os.killpg(process.pid, signal.SIGTERM)
        else:
            os.kill(hol_pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        if hol_pid is None:
            # Before readiness, let group members handle TERM before escalation.
            deadline = time.monotonic() + 3
            while time.monotonic() < deadline:
                process.poll()
                try:
                    os.killpg(process.pid, 0)
                except ProcessLookupError:
                    break
                time.sleep(0.05)
        process.wait(timeout=3)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()
    # Also remove descendants if the toplevel exited unexpectedly.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def serve(argv):
    parser = Parser(description='Start a warm HOL parent; print a JSON readiness record.')
    parser.add_argument('--case-timeout', type=positive_seconds, default=30,
                        help='maximum wall seconds per case (default: 30)')
    parser.add_argument('--startup-timeout', type=positive_seconds, default=180,
                        help='maximum HOL initialization seconds (default: 180)')
    parser.add_argument('--provenance-output', metavar='PATH',
                        help='persist a private startup manifest atomically; never overwrite PATH')
    args = parser.parse_args(argv)
    if args.provenance_output:
        unused_path, descriptor = output_location(args.provenance_output)
        os.close(descriptor)
    for name in ('wire.cmo', 'replay.cmo', 'hol_input.cmo'):
        if not (ROOT / 'build/frontend' / name).is_file():
            raise ValueError('missing bytecode; run sh scripts/build-hol-frontend.sh first')
    for name in ('hol/environment.ml', 'frontend/hol_check.ml', 'frontend/hol_server.ml'):
        if not (ROOT / name).is_file():
            raise ValueError(f'missing startup dependency: {name}')
    libraries = {}
    for package in ('zarith', 'yojson'):
        query = subprocess.run(['ocamlfind', 'query', package], check=True,
                               capture_output=True, text=True, timeout=10)
        libraries['HOL_RUNNER_' + package.upper()] = query.stdout.strip()
        if not (Path(query.stdout.strip()) / (package + '.cma')).is_file():
            raise ValueError(f'missing {package} bytecode library')
    stopped = False

    def interrupt(signum, frame):
        nonlocal stopped
        stopped = True

    previous = {sig: signal.signal(sig, interrupt) for sig in (signal.SIGTERM, signal.SIGINT)}
    process = None
    hol_pid = None
    tail = bytearray()
    try:
        with tempfile.TemporaryDirectory(prefix='hol-run-', dir='/private/tmp') as directory:
            endpoint = str(Path(directory) / 's')
            marker = ('HOL_RUNNER_READY_' + secrets.token_hex(16)).encode()
            ready_pattern = re.compile(re.escape(marker) + rb':([0-9]+)\r?\n')
            os.chmod(directory, 0o700)
            environment = {**os.environ, **libraries, 'LINE_EDITOR': 'env',
                           'HOL_RUNNER_ROOT': str(ROOT),
                           'HOL_RUNNER_SOCKET': endpoint,
                           'HOL_RUNNER_CASE_TIMEOUT': str(args.case_timeout),
                           'HOL_RUNNER_READY': marker.decode()}
            environment.pop('HOL_ML_PATH', None)
            started_at = utc_now()
            before = project_snapshot(ROOT)
            process = subprocess.Popen(['hol.sh'], cwd=ROOT, env=environment,
                                       stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                process.stdin.write(BOOTSTRAP)
                process.stdin.close()
                deadline = time.monotonic() + args.startup_timeout
                ready = False
                scan_tail = b''
                with selectors.DefaultSelector() as selector:
                    selector.register(process.stdout, selectors.EVENT_READ)
                    while not stopped:
                        if not ready and time.monotonic() >= deadline:
                            raise TimeoutError('HOL initialization timeout')
                        for key, events in selector.select(0.1):
                            chunk = os.read(key.fileobj.fileno(), 65536)
                            if not chunk:
                                raise RuntimeError('HOL process exited or closed its output')
                            tail.extend(chunk)
                            del tail[:-LOG_LIMIT]
                            scanned = scan_tail + chunk
                            if HOL_ERROR.search(scanned):
                                raise RuntimeError('HOL reported a load/runtime error')
                            ready_match = ready_pattern.search(scanned)
                            if not ready and ready_match:
                                hol_pid = int(ready_match.group(1))
                                if hol_pid <= 1 or os.getpgid(hol_pid) != process.pid:
                                    raise RuntimeError('invalid HOL readiness process')
                                private_socket(endpoint)
                                provenance = publish_provenance(
                                    ROOT, before, directory, endpoint, hol_pid, args, started_at)
                                ready = True
                                print(json.dumps({'socket': endpoint, 'supervisor_pid': os.getpid(),
                                                  'case_timeout_seconds': args.case_timeout,
                                                  **provenance}), flush=True)
                            scan_tail = scanned[-512:]
                        if process.poll() is not None:
                            raise RuntimeError('HOL launcher exited unexpectedly')
            finally:
                stop_process(process, hol_pid)
                process.stdout.close()
    except Exception:
        if tail:
            print('HOL log tail (bounded):\n' + tail[-8192:].decode('utf-8', errors='replace'),
                  file=sys.stderr)
        raise
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)
    return 0


def main():
    try:
        if sys.argv[1:2] == ['--serve']:
            return serve(sys.argv[2:])
        return client(sys.argv[1:])
    except KeyboardInterrupt:
        print('HOL fault: interrupted; no verdict received', file=sys.stderr)
        return 3
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
        print('HOL fault: ' + diagnostic(str(exc)), file=sys.stderr)
        return 3


if __name__ == '__main__':
    sys.exit(main())
