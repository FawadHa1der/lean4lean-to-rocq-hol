# Rocq Init: Delayed-Allocation/Batched-Beta Profile

## Result

One full Init attempt, fuel 512, `--progress 1`, upstream 500-second wall cap.
The immutable new binary timed out after **500.187 seconds**, exit `-9` after
the driver's deadline kill. This is a timeout, not rejection, acceptance, or
an explicit resource decline. There was no OutOfFuel diagnostic and no retry.

The final active admission was the single theorem
**`Array.foldlM_toList.aux._unary`**, original NDJSON line **120590**.
Exactly **1703 declaration records** had been admitted before it. Its progress
event occurred at 129.119 wall seconds / 128.030 CPU seconds; no next event
arrived during the remaining **371.068 wall seconds**. The declaration has name
index 10948, type expression 101708, value expression 107796, and level parameter
indices `[14, 118, 1842]`. No mutual-batch ambiguity applies to this record.

Progress is emitted *before* adapter conversion and admission. It identifies
the active declaration precisely but does not, by itself, locate the terminal
stall inside an adapter or core function. The single CPU sample described below
was collected earlier, on a different theorem. It must not be attributed to
this final stalled declaration.

## Provenance

Run directory:
[`arena/large/profile-runs/20260929T192930Z-delayed-beta`](../arena/large/profile-runs/20260929T192930Z-delayed-beta/).
The parent announced the delayed-method-allocation and batched-beta full build
ready before this worker copied it. No build or source changes were performed
by this profiling task.

| Item | Identity |
| --- | --- |
| Checker snapshot | `b88c4a832285060dc6a41cc0ccacf4f175b3e0a6f02b6014943575abfc0fb209`, 2,182,736 bytes |
| Original Init input | `620502ac9e63ba4a2dea9d46386c2f6aebc49faf8848ea3aaa18a77a09491a6a`, 347,555,345 bytes / 6,487,065 lines |
| Stable subset manifest | `998cf84342463ad1d218b9857dcf3560d3823831773133d2f334d642abb879fd` |
| Format / Lean | NDJSON 3.1.0 / Lean 4.34.1, githash `5045d0056413266e57c625dcd7c365b10e377c52` |
| Published Arena revision | `03b21e119045304d38249f426fcd86171fc253c5` |
| Exporter revision | `66f1fb4bc256072069767fce52d39480e4524869` |
| Checker start / report completion | 2026-09-29 19:29:41.365926 / 19:38:01.687897 UTC |

The native snapshot was made read-only. Its hash matched the shared binary both
sides of the copy and after execution. Input hashes matched the stable manifest
before and after execution and again during prefix extraction. Observed source
hashes did not change during the run; these are recorded build-input identities,
not a reproducible-build attestation. The unchanged shared native binary was
also checked afterward.

The run directory retains `provenance.json`, `manifest.snapshot.json`,
`profile_init.snapshot.py`, `report.json`, `progress.jsonl`, full checker logs,
`sample.txt`, `sample-driver.log`, `sample-context.json`, and
`sample-summary.json`. Stderr is 102,977 bytes, stdout is empty, neither truncated.
The checker and sampler were both waited/reaped. A final process-table audit
also found neither the recorded driver nor checker PID running.

## Phases

| Event or interval | CPU seconds | Observed wall seconds |
| --- | ---: | ---: |
| Parse interval | 8.574 | 8.606 |
| Schedule interval | 24.049 | 24.112 |
| Start of actual checking | 32.626 | 33.042 |
| Start of final active declaration | 128.030 | 129.119 |

Intervals are differences between emitted phase stamps. Wall stamps are receipt
times, not instrumentation inside the kernel. About 467.145 wall seconds were
available after checking began. No terminal CPU stamp exists because the process
was killed at the deadline. This is not merely a parser/scheduler timeout.

## Single CPU Sample

The driver invoked `/usr/bin/sample 55564 5 1 -mayDie -file sample.txt` once:
five seconds, one-millisecond requested interval, from wall second 111.713 to
116.958 including sampler startup/reporting. The trigger was 15 seconds without
declaration progress. Sample exit code was 0, with 3,747 main-thread stack samples
and a reported physical footprint/peak of 652.6M.

Before and after sampling, the active theorem was original line **94434**:
`_private.Init.Data.Range.Polymorphic.Nat.0.Std.PRange.instLawfulHasSizeNat._proof_2`.
Here `0` is a numeric name component, shown as `[0]` in the machine-readable
prefix audit to distinguish it from a string component. This theorem subsequently
finished: **20.791 CPU / 21.201 wall seconds** between adjacent declaration
events, the slowest completed admission in this run.

| Exclusive leaf symbol | Samples | Percentage |
| --- | ---: | ---: |
| `name_eqb` | 2153 | 57.46% |
| `eqb1` (extracted ASCII equality) | 1066 | 28.45% |
| `find_decl` | 257 | 6.86% |
| `eqb2` (extracted string equality) | 251 | 6.70% |
| All other leaves | 20 | 0.53% |

The call-tree analysis accounts for all 3,747 samples. Counting each function at
most once per sampled stack, `find_decl` appears in **99.07%** of stacks,
`core_reduce_nat` in **65.81%**, `core_ctor_shape` in **52.74%**, and
`core_nat_ready` in **38.46%**. These inclusive percentages overlap and must not
be added. Tail-call elimination/inlining can also remove callers from stacks.

**Supported diagnosis:** the sampled theorem spends nearly all sampled execution
in declaration lookup and structural name/string comparisons, not transport
scheduling or beta-substitution leaves. The source explains a substantial path:
`core_reduce_nat` checks `core_nat_ready env` before inspecting the candidate
head/arguments (`rocq/Checker.v:313`); readiness searches for Nat and both
constructors (`rocq/Checker.v:79`, `core_ctor_shape` at line 65).
`find_decl` scans a declaration list (`rocq/Syntax.v:303`), calling recursive
name equality (`rocq/Syntax.v:14`). The extracted mappings are
`rocq/lean_arena.ml:967` (ASCII equality), `:1014` (string equality), `:1042`
(name equality), and `:1558` (lookup), as hashed in run provenance.

**Candidate follow-up, not implemented:** move unchanged Nat-shape gates behind
the existing syntactic/operation dispatch where result equivalence can be
proved, or supply an extensionally equivalent indexed environment lookup.
Actual Nat reductions must retain all shape and safety checks. Any cached
readiness result needs an explicit environment-validity invariant; do not use
unconditional trust flags or a process-global cache. This sample does not prove
that either change solves the separate terminal Array theorem stall.

## Reproducible Diagnostic Prefixes

Both files below are exact original bytes from byte zero through the stated
declaration's ending newline. No table IDs, bodies, metadata, or declarations
inside the prefix were rewritten or removed.

| Prefix | Bytes | Records / batches | Expression nodes | SHA-256 |
| --- | ---: | ---: | ---: | --- |
| `init-through-line-120590.ndjson` | 6,253,436 | 1704 / 1704 | 107797 | `dce08f76af5892eda7110dc6b5d382d2a1a8cc07bcd8a0116b7e4b5d50a23877` |
| `init-through-line-94434.ndjson` | 4,865,221 | 1521 / 1521 | 83459 | `846760ab10763b75c62570405d6704377e2ae107d5fb189464edbfb0dea3922a` |

Sibling JSON audits report no missing referenced constants or metadata members,
no forward dependency outside its own batch, and exact agreement with the
full run's observed batch lines and prior-checked counts. The audit includes
opaque/theorem bodies, recursor RHS expressions, projection owners, implicit
Nat/String/Eq dependencies, and complete mutual groups. Thus these prefixes
preserve the preceding declaration-admission sequence and environment for their
target; they are not minimized dependency closures.

Static expression analysis provides an additional size bound: the stalled Array
theorem's body has 6,358 unique nodes, maximum depth 140, and 114,205 nodes if its
wire DAG is expanded as a tree. The sampled theorem's body has 2,069 unique
nodes, depth 59, and 206,141 expanded nodes. These counts do not unfold constants
or predict checker work or required fuel.

**No checker was run on either extracted prefix.** They are reproducible
diagnostic inputs, not separately validated verdicts, new Arena cases, or full
Init coverage. The manifest remains untouched. One full Init run and one CPU
sample were the entire checker/profiler execution budget used here.

## Tool Verification

New helpers live only under `arena/large/profile-runs/`: `profile_init.py`
(bounded snapshot/run/sample), `summarize_sample.py` (existing sample analysis),
`extract_prefix.py` (byte-preserving extraction/dependency audit), and
`test_profile_tools.py`.

`python3 -B -m unittest discover -s arena/large/profile-runs -p test_profile_tools.py -v`
passed **18 tests**. Coverage includes positive closure/order, missing and forward
dependencies, implicit dependencies, opaque bodies, recursor RHS, mutual grouping,
sample recursion accounting/conservation, fingerprinting, and child kill/reap.
The full run additionally exercised the actual deadline, sampler, snapshot
integrity checks, and process cleanup. No existing source, runner, main manifest,
build file, or shared binary was edited.

## Prefix Validation Follow-Up

The earlier "no checker was run on either extracted prefix" statement describes
the initial profiling stage. The user subsequently authorized exactly two prefix
runs against the **same immutable `b88c4a83...0fb209` snapshot**, with fuel 512,
`--progress 1`, at most 120 seconds each, and one sample per run only if still
running at 30 seconds. Both were executed sequentially; **full Init was not run
again**. A 119-second enforced deadline leaves process-cleanup headroom under
the requested 120-second maximum.

Reports and their sibling logs/provenance/samples:

- [94,434-line prefix report](../arena/large/profile-runs/20260929T194909Z-b88-validation-prefix-94434/report.json).
- [120,590-line prefix report](../arena/large/profile-runs/20260929T194909Z-b88-validation-prefix-120590/report.json).

| Prefix end line | Actual exit | Classification | Wall seconds | Checked-record evidence |
| --- | ---: | --- | ---: | --- |
| 94434 | 0 | **accept** | 84.426 | Stdout: `accept: 1521 declarations checked by extracted Gallina` |
| 120590 | -9, deadline kill | **timeout**, no logical verdict | 119.023 | Last progress: line 120590, `checked=1703`, `Array.foldlM_toList.aux._unary` |

The accepted prefix entered its final theorem at 63.747 wall seconds and exited
20.679 seconds later. This confirms that the smaller prefix really checks through
the sampled range theorem and reproduces its slow admission without an
unknown-constant failure. In the larger prefix, the same range theorem also
completed, taking 21.906 CPU / 22.567 wall seconds between declaration events.

The Array prefix reached its final theorem at **104.359 wall / 101.194 CPU
seconds**, then emitted no further progress for **14.664 wall seconds** before
the deadline kill. It reproduces the exact full-run stopping declaration and a
bounded timeout, **not a separately observed 371-second stall**. Its final
logical verdict remains unknown. No unknown-constant or OutOfFuel diagnostic
appeared in either run; all 1,703 preceding records actually completed admission
in the Array run. No acceptance is inferred for the interrupted final theorem.

Both observed `(source line, checked count)` declaration-event sequences exactly
match the corresponding beginning of the saved full-Init run: 1,521 events for
the accepted prefix and 1,704 for the Array prefix. This supplements the earlier
static dependency audit with actual execution evidence and rules out a changed
admission order in these attempts.

Transport was small: the accepted prefix used 0.093 CPU seconds parsing and
0.094 scheduling; the Array prefix used 0.119 and 0.109, respectively. Checking
began at 0.190 and 0.232 wall seconds. Timing is a single shared-machine
measurement, not an isolated comparative benchmark.

### Samples And Attribution

Each run was still alive at 30 seconds, and each received exactly one successful
five-second, one-millisecond-interval requested sample. Both sampler exit codes
were 0. The windows include sampler startup/reporting overhead.

| Prefix | Sample wall window | Observed checked-count bounds | Progress events during window | `find_decl` inclusive |
| --- | --- | --- | ---: | ---: |
| 94434 | 30.014-35.296 s | 1190 to 1260 | 70 | 3702/3748 stacks, 98.77% |
| 120590 | 30.013-35.636 s | 1186 to 1236 | 50 | 3693/3745 stacks, 98.61% |

These counts are **progress lower bounds, not attribution to a single theorem**.
The first window advances from line 63014 (`Membership`'s inductive batch) through
line 68875 (`Lean.Omega.IntList.combo_eq_smul_add_smul`); the second advances from
line 62870 (`Lean.Omega.IntList.dot_mod_gcd_left`) through line 67428
(`Lean.Omega.tidy_sat`). Neither sample directly covers the final range or Array
theorem. All intervening events and names are retained in `sample-context.json`
and `progress.jsonl`, and both reports explicitly set
`single_observed_active_declaration=false`.

The first sample's exclusive leaves were name equality 52.85%, ASCII equality
30.90%, string equality 8.72%, and lookup 6.83%. The second recorded 53.38%,
28.81%, 9.16%, and 7.77%, respectively. These confirm the same broad lookup/name
comparison hotspot across earlier admissions, without attributing it to the
unsampled terminal Array stall.

### Integrity And Scope

Binary and prefix hashes matched their pinned values before and after both runs;
neither log was truncated. The driver reaped both checker children and both
samplers, and a final process-table audit found none of the recorded driver,
checker, or sampler PIDs running. No retry, full-Init execution, replacement
binary, core change, or manifest edit was performed.

New files: `arena/large/profile-runs/profile_prefixes.py`,
`arena/large/profile-runs/test_prefix_profile.py`, and the two run directories
linked above. Existing helper code and original run artifacts remain unchanged.
The driver and helper were copied and hashed in each run directory for provenance.

`python3 -B -m unittest discover -s arena/large/profile-runs -p 'test_*.py' -v`
passed **24 tests**: the prior 18 plus six for actual-exit classification,
multi-declaration sample windows, stable windows, interrupted samples, parse-stage
sampling, and absent samples. The prefixes remain diagnostic derivatives, not
additional Arena coverage or acceptance of full Init.

## Dispatch Checkpoint Target Profile

The next authorized experiment ran **only the saved 120,590-line prefix**, once,
with fuel 512 and `--progress 1`. It did not run full Init or another prefix.
The new [report](../arena/large/profile-runs/20260929T205000Z-dispatch-array/report.json)
and [provenance](../arena/large/profile-runs/20260929T205000Z-dispatch-array/provenance.json)
are separate from every earlier result. The checker and input were copied into
this new run directory and made read-only before execution.

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `build/rocq-check-dispatch-checkpoint` and private run copy | 2,182,736 | `3ef3328088cc6f91a4113947ffb6d97196e840bcb4f6d9445512fa9e5ef86be3` |
| Exact original prefix and private run copy | 6,253,436 | `dce08f76af5892eda7110dc6b5d382d2a1a8cc07bcd8a0116b7e4b5d50a23877` |
| `report.json` | See artifact | `27403a8017966dfcf1e04dd4ef1348b506036938e83123a505995ee1ae290b3a` |
| `sample.txt` | See artifact | `93cefa6488de7a4b94283d1c7e4d106cd84c05a9f8c5dfc05a3cb7fd8795c017` |
| `sample-summary.json` | See artifact | `07e35875073be9b7125c8b25f1725bfd545d0081841d97359ffc72ef99425167` |

The prefix retains the earlier dependency audit and NDJSON 3.1.0 metadata:
1,704 declaration records/batches and 107,797 expression nodes. All observed
`(line, checked)` declaration events in this attempt match the original full
`b88` run's prefix exactly. This checks admission order, not frontend identity
or equality of all intermediate computations.

### Actual Outcome

Started 2026-09-29 20:50:05.902 UTC; checker killed and reaped at the enforced
149-second deadline, leaving headroom under the user's 150-second maximum.

| Event | Wall seconds from launch | Checker CPU seconds |
| --- | ---: | ---: |
| Parse begins | 0.188 | 0.003 |
| Schedule begins | 0.317 | 0.132 |
| Checking begins | 0.440 | 0.255 |
| Target begins, line 120590, checked 1703 | 34.219 | 32.754 |
| Sampler starts after 10.011 quiet seconds | 44.230 | No new progress measurement |
| Sampler finishes, actual exit 0 | 50.055 | No new progress measurement |
| Checker deadline kill, actual exit -9 | 149.017 | No final CPU event |

Parsing took 0.129 CPU seconds and scheduling 0.123. The checker completed all
1,703 preceding records, then remained at
`Array.foldlM_toList.aux._unary` for **114.798 wall seconds** through process end.
Classification is **timeout, no logical verdict**. There was no unknown-constant,
OutOfFuel, or other non-progress diagnostic; stdout was empty. The 101,635-byte
stderr log was not truncated. This is neither acceptance nor rejection of the
target or full Init, and it does not establish an infinite loop.

### Target-Correlated Sample

The driver required the latest event to identify exactly line 120590, checked
1703, and the target name, followed by at least ten seconds without another
event. It requested **one** five-second sample at one-millisecond intervals.
The 44.230-50.055 wall window includes sampler startup/reporting overhead.

[Sample context](../arena/large/profile-runs/20260929T205000Z-dispatch-array/sample-context.json)
retains the before/after event and the empty intervening-event list; the sampler
exited 0 and the checker remained alive. Thus this sample covers the target's
admission, unlike the earlier blind-30-second samples spanning many declarations.
`checked=1703` remains a completed-record lower bound, not acceptance of record
1704. No subsequent progress or final checker verdict appeared.

The [sample summary](../arena/large/profile-runs/20260929T205000Z-dispatch-array/sample-summary.json)
accounts for all **4,076 stacks**, counting recursive appearances of a function
once per stack for inclusive totals:

| Function | Inclusive stacks | Percentage |
| --- | ---: | ---: |
| `sort_of` | 3963 | 97.23% |
| `find_decl` | 3926 | 96.32% |
| `core_infer_projection` | 3510 | 86.11% |
| `get_constant` | 2629 | 64.50% |
| `core_nat_ready` | 417 | 10.23% |

Inclusive rows overlap and must not be summed. Exclusive leaves were structured
name equality 57.58%, `find_decl` 19.97%, ASCII equality 15.24%, and string equality
4.39%, together 97.18%. Reported physical footprint and peak were both 37.0 MB.

The reproducible bottleneck in this window is environment lookup/name comparison
within inference, with substantial projection and sort inference on the stacks.
Current source context is consistent with this: `Checker.v`'s `get_constant`
uses `find_decl`, while `core_infer_projection` recursively infers the value,
looks up its inductive/constructor metadata, and calls `sort_of`.
The sample does not count lookup calls, identify their queried names, establish
the complexity of repeated inference, or predict the benefit of an index.
The separate [index benchmark](ENVIRONMENT_INDEX_BENCHMARK.md) still has substantial
allocation and workload caveats; this profile is not approval to integrate it.

### Provenance And Limits

Original checkpoint, original prefix, and both run copies matched their pinned
hashes before and after execution. The driver/helper snapshots are retained.
Observed before/after shared-source hashes also matched, including:

- `frontend/wire.ml`: `4e204f626e9dd61a049c5d1bc60b2aaaddab597e7770e0922c68fa017d82d802`.
- `frontend/replay.ml`: `4be904adc035610223b13f71479da21969729f40a4142b80374d4b5e50ddb228`.
- `frontend/rocq_adapter.ml`: `a497380a7ac2b4ffd0bfa6fd2e234c97d1d99a778e9d8c7213fc1e5ad59e0ac5`.
- `frontend/rocq_main.ml`: `743b134c257c43a67dcdac768baa0f792cc854139fd524d34179858f0b25b53b`.
- `rocq/Checker.v`: `bdd3d477db4d16796e48f9e57067cebcf8b2cfd49449888d28e70d8f7780d745`.
- `rocq/Syntax.v`: `e8ae6fe46f8ab2581f97e9f7f505e59e26796f41091700ec91936fdd5a352be9`.
- `rocq/lean_arena.ml`: `ce9a1985c21cba076e60e6aca53a9b843d6c76f57771cba5ebcaf5e7cd366ef1`.

These are observed source context, **not an independently established build
attestation** for the provided checkpoint. In particular, no frontend equivalence
with the private `82a` executable is assumed. The new target entry at 34.219 wall
seconds versus 104.359 in the earlier `b88` prefix run is an observation from
different snapshots on a shared machine, not an isolated dispatch speedup claim.
The older full-run range-theorem sample is not retroactively attributed to Array.

Both child processes were reaped; a final process-table check found none of
driver PID 71604, checker PID 71641, or sampler PID 75205 remaining. No retry,
fuel increase, full Init execution, build, production source edit, existing
binary replacement, or manifest edit was performed.

New helpers are `arena/large/profile-runs/profile_array_dispatch.py` (SHA-256
`00f64fd530b699409cca38eb67a59fdd11c57bb6ecb29c3bff0866ce8afb3518`) and
`test_array_dispatch_profile.py` (SHA-256
`d286479d9baf710ef5e68d21ec70b5df8858a7846c7d8c56186796b1fc8029ca`).
The same helper-suite command above passed **34 tests**: the previous 24 plus ten
for exact target identity/count/stage, quiet time, newer events, sample budget,
and refusing a blind elapsed-time trigger. The actual run additionally exercised
the trigger, one successful sampler, timeout, integrity checks, and cleanup.
