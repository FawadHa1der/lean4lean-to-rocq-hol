# Warm HOL Light Runner

The runner initializes ordinary HOL Light once, then forks a fresh child for
each input. Only the child calls `Hol_check.check_file : string -> int * string`.
All HOL state mutated while checking a case is private to that child. This is
process isolation for sequential cases, not a sandbox for hostile OCaml code.
Neither runner nor client reads Arena manifests or expected verdicts.

## Start and Check

From the repository root:

```sh
sh scripts/build-hol-frontend.sh
sh scripts/hol-server.sh --case-timeout 30 --startup-timeout 180
# Optional persistent startup manifest; PATH must not exist:
sh scripts/hol-server.sh --case-timeout 30 \
  --provenance-output /private/tmp/hol-startup-unique.json
```

The server stays in the foreground. After successful initialization it prints
one JSON object containing `socket`, `supervisor_pid`,
`case_timeout_seconds`, `provenance_path`, and `provenance_sha256`.
With the optional export flag it also contains `provenance_output`.
The two startup commands above are alternatives, not two required servers.
In another terminal, use the reported socket:

```sh
python3 scripts/hol-check.py --socket /private/tmp/hol-run-EXAMPLE/s \
  --timeout 30 /absolute/path/to/case.ndjson
python3 scripts/test_arena.py \
  --checker 'python3 scripts/hol-check.py --socket /private/tmp/hol-run-EXAMPLE/s --timeout 30' \
  --timeout 40 --report /private/tmp/hol-arena-report.json
```

The generic Arena harness appends the filename. Paths are JSON data, never
OCaml source or shell expressions. Relative input paths are made absolute by
the client. `-`/stdin input is deliberately unsupported. Missing input files
are handled by the checker, not reclassified as malformed source by the runner.

The actual case limit is the smaller of the client request and the server's
`--case-timeout`. The client IPC deadline is its requested timeout plus
`--transport-grace` (default 5 seconds). Set the Arena harness timeout higher
than both. Run one harness against each server; queued concurrent requests may
hit their client deadline. Parallel workers should each start their own server.

## Exit Codes

| Code | Meaning |
| --- | --- |
| 0 | Checker acceptance. |
| 1 | Checker rejection of malformed input. |
| 2 | Checker decline, including unsupported input or unsuccessful proof search. |
| 3 | Checker or runner fault; no logical verdict. |

A server-enforced wall timeout returns **2**, with explicit timeout diagnostics,
only after SIGKILL and `waitpid` have removed the case child. Abnormal child
termination, invalid checker codes, unexpected exceptions, malformed protocol,
startup errors, broken sockets, and client transport timeouts return **3**.
A transport timeout does not establish that a case exceeded its checking budget.
Unsupported proof search is not evidence of invalidity.

## Startup and Lifecycle

The shell wrapper uses `scripts/toolchain-exec.sh`. The supervisor supplies
fixed source text to normal initialized `hol.sh` stdin, with `LINE_EDITOR=env`.
It adds the Zarith and Yojson library directories discovered by `ocamlfind`,
then loads `unix.cma`, `zarith.cma`, `yojson.cma`, `build/frontend/wire.cmo`,
`build/frontend/replay.cmo`, and `build/frontend/hol_input.cmo`. The three
project bytecode loads use absolute paths passed via the environment, not
interpolated OCaml source. It enables HOL loader failures, restricts project
`needs` lookup to the absolute project root, and loads
`hol/environment.ml`, `hol/primitive_validation.ml` and `hol/text_validation.ml`
before loading `frontend/hol_check.ml`, then `frontend/hol_server.ml`.
The frontend and server use ordinary OCaml identifier lexing
(`unset_jrh_lexer`) after the HOL admission code has loaded. This permits the
frontend's short module aliases and standard `Unix` constructor names. HOL
term quotations remain available; uppercase HOL tactic identifiers should not
be introduced directly into this frontend without adjusting its loader.
The existing HOL initialization override `HOL_ML_PATH` is cleared.

A unique readiness marker is emitted only after the initialized server binds
its socket. The supervisor also scans initialization output for HOL errors:
the REPL exiting zero alone does not prove successful initialization. Startup
has a separate bounded deadline. Dependency loading or parser failures fail
closed without printing a readiness record.

Sockets are unique, shorter than 100 bytes, beneath a fresh mode-0700 directory
in `/private/tmp`, and explicitly mode 0600. No TCP listener is used. Existing
sockets are never overwritten. The client checks socket ownership and modes.
The server handles one request at a time, with bounded request-read and
response-write deadlines. A disconnect during checking kills and reaps the
child. After each child, the parent continues from its pre-case HOL state.

Stop with Ctrl-C or send SIGTERM to the reported `supervisor_pid`. The HOL
parent kills and waits for its active child; the supervisor waits for shutdown,
then removes its private directory. An unresponsive shutdown has a process-group
SIGKILL fallback. As with any process, SIGKILL of the supervisor itself cannot
run cleanup; use SIGTERM for orderly teardown.

HOL startup output is drained continuously into a 64-KiB in-memory tail; on
failure only its last 8 KiB are printed. No unbounded log file is created.
Case stdout/stderr go to `/dev/null`; the structured checker diagnostic is
bounded to 4096 bytes (non-ASCII/control bytes are replaced with spaces).
Request frames are at most 16 KiB; response frames are at most 32 KiB.

## Startup Provenance

Before launching HOL, the supervisor records a bounded SHA-256 snapshot of
local **project inputs**. On receiving HOL's internal readiness marker it
recomputes the closure and all hashes. It publishes the public JSON readiness
record only if both snapshots are identical and manifest publication succeeds.
A changed, missing, unreadable, redirected, or oversized input faults with exit
3; the HOL process is stopped/reaped and no public readiness is printed.
The internal socket exists briefly during this check; its private random path
has not yet been announced. Do not discover or use sockets before public READY.

The snapshot contains:

- Exact bootstrap bytes represented by SHA-256 and length, plus on-disk
  `scripts/hol-check.py`, `hol-server.sh`, `toolchain-exec.sh`, and
  `toolchain-env.sh` hashes.
- Source roots `hol/environment.ml`, `hol/primitive_validation.ml`,
  `hol/text_validation.ml`, `frontend/hol_check.ml`, and
  `frontend/hol_server.ml`, recursively following literal project `needs`
  calls. Each file has its relative path, SHA-256, length, and filesystem
  identity/timestamps. The dependency graph is recorded too.
- `build/frontend/{wire,replay,hol_input}.{cmo,cmi}`: actual bytecode and
  interfaces, not a claim that current frontend source built those artifacts.

Dependency discovery reads bytes only; it never evaluates source. The bounded
lexical scanner skips nested comments, strings, character literals, and HOL
quotations. It accepts canonical literal `.ml` paths beneath `hol/` or
`frontend/`, rejects nonliteral `needs`, known alternate loader forms and
loader-path changes, and refuses symlinked project inputs/directories. This is
the current project's loader contract, not a general OCaml dependency analyzer
or a sandbox for malicious source. Literal calls in unexecuted branches are
conservatively included. New loading mechanisms require an explicit runner
update; an arbitrary program can load code outside this static contract.

The manifest has `version: 1`, `kind: hol-runner-startup-provenance`,
`scope: project-inputs-only`, `snapshot`, `snapshot_sha256`, `limitations`, and
`startup`. Startup records both equal snapshot digests, observation times,
socket, supervisor/HOL PIDs, and case timeout. The readiness
`provenance_sha256` hashes the complete manifest bytes, including the final
newline; `snapshot_sha256` hashes the runner's canonical JSON encoding of the
snapshot. Retain the readiness digest separately and compare it with the saved
file's SHA-256 before attaching it to a test report. The digest is integrity
metadata, not a signature or independently authenticated attestation.

`provenance_path` is `provenance.json` in the mode-0700 run directory. Its mode
is 0600 and it disappears on orderly shutdown. `--provenance-output PATH` on
the **server** optionally persists identical bytes at an absolute or relative
user-selected path; its parent must already exist and must not itself be a
symlink. Existing files, directories, and dangling symlinks are never replaced.
Publication writes/fsyncs a private temporary file in that parent, then uses an
atomic no-overwrite hard link, removes the temporary name, and verifies the
published file's ownership, mode, link count, length, and SHA-256. A concurrent
creator wins rather than being overwritten. Filesystems lacking this operation
fault instead of falling back to non-atomic writes. Failure to persist prevents
readiness; a file already fully published before a later failure can remain and
is not evidence that public readiness was emitted.

Limits: 512 input files, 32 MiB per input, 2 MiB per scanned source, 128 MiB
aggregate input bytes, and 1 MiB per manifest. The client arguments, request
protocol, filename-appending harness interface, and exit mappings are unchanged.

**Scope limitation:** the manifest does not hash or attest the installed HOL
kernel/source image, OCaml executable/version, Zarith/Yojson/Unix libraries,
dynamic libraries, environment, OS, or runtime state. Toolchain discovery is
unchanged and does not constitute provenance for those external dependencies.
The launcher script hashes are on-disk observations, not proof of which script
bytes the shell or Python already executed. Two matching observations catch
ordinary concurrent startup edits, including file replacement, but are not an
atomic filesystem snapshot or proof of every byte actually read by HOL. Changes
after READY are not monitored, and transient changes restored between
observations may escape detection. This is source provenance and startup
stability checking, not a runtime, semantic, kernel-soundness, or build attestation.

## Local Protocol

One UTF-8 JSON line is sent per connection. Keep the connection open until the
reply; write-half-close is treated as cancellation. Requests have exactly:

```json
{"version":1,"path":"/absolute/path/case.ndjson","timeout_seconds":30}
```

The reply has `version: 1`, `code: 0..3`, bounded `message`, and `kind` equal to
`result`, `timeout`, or `fault`. The parent obtains the child's response through
a private pipe and requires normal child exit before returning its result.
Neither filenames nor file contents are evaluated as source by the runner.

## Supervisor Shutdown

The supervisor is the sole reaper of its new-session launcher child and
requires default SIGCHLD disposition. A recorded HOL READY PID is not durable
signal authority. TERM targets only the owned unreaped launcher's group, then
the supervisor waits up to three seconds for that child. A successful reap
ends all destructive signaling; only final PID/group absence probes follow.

If grace times out, one KILL attempt requires a fresh ownership check, followed
by a final wait bounded to three seconds. A non-timeout grace-wait exception
also permits this best-effort owned cleanup, but the original error remains
fatal even if cleanup succeeds. There are no grace-period group probes,
unbounded wait fallbacks, or post-reap group kills. Surviving or uncertain
descendants after the root is reaped cause a cleanup fault, not an unsafe
attempt to kill an unowned numeric group. Permission errors remain faults.

Startup write/close failures get a guarded stdin close after process cleanup:
an open owned pipe must be made nonblocking before its buffered close is
attempted. Setup/close errors are retained; there is no blocking-flush fallback.
Primary, process-cleanup and pipe-close failures remain separately available.

Optional `HOL_RUNNER_CLEANUP_REPORT_DIR` enables atomic private JSON reports
for already-failing cleanup. Use a private directory owned by the runner user.
Reports retain operation labels, signal arguments, cached returncodes,
timestamps, original errors and final absence observations. Publication errors
remain faults too. These diagnostics do not establish the OS cause of an error
or authorize suppressing it.

## Trust Boundary

This runner provides transport, resource handling, and process isolation only.
Acceptance still depends on the frontend and HOL checker actually loaded;
runner testing does not establish checker soundness, completeness, correspondence
to Lean, or corpus compatibility. HOL's existing trusted kernel and the
frontend's transport trust boundary remain unchanged. The wall timer is a real
interval timer in the parent, independent of child cooperation. There is no
separate hard memory quota; OS termination is a fault, not acceptance or rejection.

## Verification

Runner regression tests (Python fixtures and fake processes, no native HOL):

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
  -s tests/hol_runner -p 'test_*.py' -v -f
```

Eighteen provenance tests cover transitive closure, quoted/commented decoys, unsupported
loader forms, file/closure/bytecode/interface changes, mutation during hashing,
same-byte inode replacement, missing/symlink/special inputs, bounds, private
paths, manifest digest integrity, atomic publication races, no overwrite,
unchanged client argv and 0/1/2/3 codes, and synthetic supervisor startup/refusal
and child cleanup. These tests use isolated temporary fixtures and a synthetic
readiness process, not a real HOL checker or verdict oracle. This worker did not
start a real HOL server against the concurrently edited sources; the parent's
subsequent integration is recorded below.
The Unix-socket tests require permission to bind private local sockets.

Discovery additionally registers 45 deterministic teardown controls and 14
synthetic-helper error-route controls, for 77 routine tests in this directory.
They cover bounded grace/escalation, no destructive action after reap or lost
ownership, surviving/reused groups and PIDs, retained permission/wait errors,
nonblocking stdin cleanup, and primary-plus-cleanup failure preservation.
They import `scripts/hol-check.py` and the local provenance helper through the
actual project layout, without private worker paths. The historical whole-file
source-equivalence check remains in retained private validation evidence rather
than imposing a broad frozen-source pin on routine maintenance tests.

Verified locally on 2026-09-29 with the supplied bytecode bridge and HOL checker:

- Shell syntax and Python compilation pass; the server compiles through HOL's
  actual Camlp5 preprocessor as well as loading in normal initialized HOL.
- Ten temporary transport/process regression tests cover all four exit codes,
  invalid codes, exceptions, crashes, malformed requests/replies, CLI errors,
  socket permissions, bounded diagnostics, timeouts, cancellation, mutable-state
  isolation, and PID-level confirmation of child reaping.
- Two temporary supervisor tests cover zero-exit startup failures, explicit HOL
  errors, startup timeout, 2-MiB noisy startup output with bounded retained logs,
  readiness, and graceful parent/child shutdown.
- The real warm server returns 0 for `tutorial/001_basicDef.ndjson`, 2 for
  `tutorial/002_badDef.ndjson`, 1 for synthetic malformed JSON, and 3 for a
  missing file. Tutorial requests used `test_arena.py`'s `make_command` and
  `run_process` helpers without loading a manifest or expected outcomes.
- An input path containing quotes, a newline, and OCaml-looking text remains
  data and returns the same acceptance as the original file. Blocking on a
  synthetic FIFO returns timeout/decline, followed by successful acceptance of
  another tutorial case. Shutdown removes the private directory and leaves no
  runner processes.

These are focused runner checks, not a full Arena corpus run. Those initial test
servers were stopped after verification.

### Parent Startup Integration

The parent reported successful real HOL family-server readiness at
`2026-09-29T19:49:22.643779+00:00`, with the persisted startup manifest at
`build/reports/hol-family-runtime.json`. This worker independently checked its
mode (0600), length (9570 bytes), complete-file SHA-256, and internal snapshot
digest consistency without sending a server request.

- Manifest SHA-256:
  `736c1498de3f35b9f6dbac0ace01945e2018e38a4764a0ad149d3f2cf5156847`.
- Equal before-launch and READY snapshot SHA-256, covering 25 project inputs:
  `91a9f51400578e456a512250a9dc8f26d8e14f0f8bc626fd479a69d8e6f025db`.
- Loaded-startup manifest's on-disk runner SHA-256, also matching the held file:
  `b71273f60ae608b43294530702bf8f6d180deeee6c6916270890039f342f5d8d`.

The recorded socket is `/private/tmp/hol-run-ht30uulj/s`, with a 10-second case
limit. At this handoff the server was exclusively assigned to the parent's
full Arena run. No Arena outcome or new 97-case export-suite result is implied
by startup success. The manifest remains explicitly project-only provenance,
not toolchain, dynamic-library, runtime-state, or semantic attestation.
