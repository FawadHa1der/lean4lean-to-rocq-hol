# HOL Composition Regressions

These are genuine HOL Light proof/checker tests, not an Arena replacement or
an external expected-answer oracle. All changes and reports remain local.

From the project root, first build the shared transport:

```sh
sh scripts/build-hol-frontend.sh
python3 tests/hol_composition/run.py --list
python3 tests/hol_composition/run.py history-inventory trace-empty trace-recursive trace-forged
python3 tests/hol_composition/run.py preserved-full
```

With no group arguments, the runner executes all 124 groups. Each focused group
has a 180-second wall limit; `preserved-full` has 900 seconds for all 20 existing
native suites plus a final three-invariant check. This is not a claim that the
whole matrix takes only 180 seconds. Groups after a failed group are unexecuted,
not passed. A selected run reports every unselected group explicitly.

Each invocation creates a unique `build/reports/hol-composition-*` directory.
It copies current project sources, the actual transport bytecode/interfaces,
test drivers and fixtures to a private snapshot, checking hashes before and
after acquisition. The proof assistant runs only against that snapshot. Reports
retain each driver, exact expected marker pattern, all output, options, limits,
PID/exit/reap status, process-group absence, and before/after file inventories.
The toolchain and OS remain external dependencies; this is not a hermetic image
or a proof of source-to-bytecode compilation. The toolchain symlink is deliberate.

HOL's interactive process can exit zero after a source error. Consequently,
zero exit alone is insufficient: all exact completion markers must appear once,
without compiler/loader/proof exceptions. Printed source containing a marker
is not an executed marker. Timeout, missing marker, changed source, failed
exit, or remaining process group invalidates the group.

The runner's own fifteen tests exercise those evidence/cleanup conditions:

```sh
python3 -B -m unittest discover -s tests/hol_composition -p test_runner.py -v
```

These fifteen tests are harness tests, not additional logical assertions or
additional Arena proofs. Their small shell processes deliberately simulate
success, failure, mutation and timeout; logical groups use the real HOL runtime.

## Fixtures And Boundaries

`data/arena/corpus/tutorial` contains byte-preserved, pinned-source Arena tutorial
exports. `data/fixtures/mutual` includes an authentic two-family empty-constructor
export, a first-block recursive fixture and a forged-motive control from ConLeche
commit `78ded4b6fc9a4d9ab809e8ca2c75c56537c41bff`. Its source files and Apache-2.0
license are preserved under `sources/`. The recursive fixture contains exactly
the first 183 lines of `sources/inmodel_mutual.ndjson`, through the first complete
mutual block and its Eq/Nat dependencies. It is not the entire 1,384-line export
and is not counted as a passed full Arena case. The forged copy changes only
that block's first recursor's `numMotives` from two to one. Other files
are generated positive/negative regression fixtures inherited from the reviewed
raw-constructor composition. Historical fixture manifests/reports identify their
origin; they are not current test outcomes and the checker never reads them.
`fixture-pins.json` records every copied fixture's identity and the Arena manifest
pin; every tutorial input was checked byte-for-byte against that corpus.
The runner refuses modified, missing or extra fixture files before startup.

The copied bootstrap is installed at `hol/private_boot.ml` inside each snapshot;
it is not part of the production runtime. `native.sh` is likewise copied to the
snapshot's `scripts/private-hol.sh` and launched only by the bounded supervisor.
All fixture aliases in drivers are resolved inside the isolated snapshot.

`reference_environment_rules.ml` freezes the preceding 27 native / 9 admission
rules. The boundary test parses its quotations without loading duplicate
definitions, and compares them with the new rule theorem prefixes. The new
mutual rules append one native and one admission clause; they do not replace
or reorder existing clauses. This is a prefix-preservation test, not a proof
that the new model matches all of Lean's metatheory.

Raw-history success means a closed HOL theorem about the exact **decoded**
history, policy and canonical environment. Parsing and translation are separate
trust boundaries. A name-inventory check permits declaration-table order to
differ, but requires no duplicates, omissions, additions or renames. The trace
still authenticates complete metadata and types. Constructor order within a
family, recursor rules, motives and parameters are not erased or sorted away.

## Indexed/Raw/HAdd Composition

The registry preserves all 49 preceding main groups, including the 18 optional
arithmetic groups. It adds30 indexed/raw groups and15 prefixed `hadd-*` groups.
The native/admission totals are29/11, with exact old28/10 and27/9 ordered-prefix
tests. Count guards change only their expected totals; optional arithmetic,
reflection, NI/get helpers and the core engine are not replaced.

The HAdd groups retain the reviewed typed negative controls, authenticated
original histories, both raw-function exports119/120, the certified static
premise check, and an exact mixed119/HAdd history. The first132 records of the
retained full `data/sources/hadd/app-lam.ndjson` are byte-identical to the HAdd
fixture; the full source is not a claimed checker acceptance. Mixed fixtures
remap table IDs only. `fixture-pins.json` records source and fixture hashes.

The new raw scope is nonrecursive, universally nonzero polymorphic families;
the existing raw function-recursive slice stays nonindexed Type0. Neither
permits arbitrary raw indexed-mutual normalization. Certificates prove exact
closed `l4_input_valid policy canonical_environment original_decoded_history`,
not validity of a flattened raw environment or full Lean correspondence.

The original optional reflection smoke is run separately with
`python3 -B scripts/test-hol-reflection.py --smoke --stage-cap 180`.
Its 25 boundary checks and 17 synthetic runner tests are separate from native
suite counts. The newer prepared API and runner hooks are preserved, with their
two added test modules' rule guards adapted to 29/11. Run their separate focused
replay with `python3 scripts/test-hol-unified.py focused`; registration and source
composition alone do not establish a passing proof replay.

Unsupported cases and bounded proof-search failure decline. Expected declines
in negative regressions establish only fail-closed behavior, not a theorem of
Lean invalidity. No new HOL axiom, logical oracle, unchecked deserialization,
or serialized expected-answer input is used.

## Closed Computation And Comparisons

Three `closed-computation-*` groups exercise the theorem-backed shortcut for
closed lifting, substitution and instantiation. Their actual-main replay passes
6,154 assertions. The separate pure retention-accounting suite passes 83,391
assertions; these are not 83,391 additional Lean proofs. The 94 preceding groups
are undergoing a fresh frozen-main replay after the shortcut's integration.

The opt-in `Nat.beq` / `Nat.ble` API contributes 27 more groups: `bool-general`
and 13 cases for each operation. Cases cover empty, Nat and dependent contexts;
beta/let/named bodies; missing or forged premises; incorrect symbolic equations;
and bodies that agree on finite examples but fail the general contract. The
fresh frozen-main matrix passes 1,185 assertions across all 27 groups, with
282 source pins unchanged and all child processes reaped. Its sealed audit is
`build/workers/hol-bool-derived/evidence/fresh-main-native-audit.json`. No
default proof-file dispatch is enabled by registering these groups.

All previous job definitions and deadlines remain unchanged. Counts describe
registered groups, not a passing full matrix on every subsequent source change.
The separate add-body runner remains under `tests/hol_add_body`; its six passing
main groups are not additional jobs in this registry.
Likewise, `python3 -B tests/hol_shift_left/run.py` runs ten separate opt-in
shiftLeft groups. Their fresh frozen-main replay passes 357 assertions, audited
under `build/reports/shift-left-main-audit-20261001T032945Z-8917`; they are not
additional jobs or assertions of this 124-group registry.
