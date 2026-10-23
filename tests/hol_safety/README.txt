OPT-IN RESTRICTED-DEFINITION SAFETY SUITE

This suite does not change the shared composition registry or default server.
The full feature and current-main insertion patch require parent review and
authorization before integration. Do not run native gates while a source or
native-slot hold is active.

After authorized integration, from the project root:
  python3 -B -m unittest discover -s tests/hol_safety -p 'test_*.py' -v
  sh tests/hol_safety/build_frontend.sh
  python3 -B tests/hol_safety/run.py --prepare-only
  python3 -B tests/hol_safety/run.py

The build script compiles actual transport modules and runs transport controls.
It does not run HOL. It refreshes build/frontend bytecode; coordinate that write
with other main tests. Prepare-only captures actual sources/runtime but does
not prove or run the nine groups. The final command makes its own fresh capture.

The native runner starts general, single, mutual, references, authentication,
shape, atomicity, wrappers, then arena. Each group retains the existing 180s cap.
The two Arena fixtures are gated on all eight focused groups passing. A first
failure stops the sequence and is retained. No full Arena or shared composition
matrix is implicitly launched. Assertion counts are measured, not precomputed
logical verdicts. Native sources are real modules, not offline signature stubs.

The load_phases.ml file MUST be concatenated into interactive stdin by run.py,
not loaded with needs. Distinct top-level lexer phases load transport (ordinary),
proof modules (JRH), ordinary frontend, then the opt-in safety adapter (JRH).
The runner requires all four markers, real executable/cwd identity, exact closed
certificate controls, unchanged axiom inventory, and leader/group cleanup.

Routine tests check only the nine safety jobs/caps, safety loading/protocol and
semantic guards, and the new fragment_check helper. They allow unrelated shared
registry additions and changes outside that helper. test_maintenance.py exercises
those permitted changes and verifies that actual safety-job/cap/guard violations
still fail. These are offline source/protocol tests, not HOL soundness proofs.

baseline/ retains the ORIGINAL reviewed main pins and unmodified environment,
byte-for-byte. They belong to a ONE-TIME integration preservation gate, not
routine unit discovery or native startup. No baseline was refreshed to approve
later K/dispatcher/registry changes. Explicitly invoke this gate only when
auditing the original integration against that historical baseline:
  python3 -B tests/hol_safety/integration_preservation.py --root "$PWD" --stage before
  python3 -B tests/hol_safety/integration_preservation.py --root "$PWD" --stage after
The before stage expects the original environment without fragment_check; after
expects exactly the two insertions and otherwise the original whole file.
Both stages require all original thirteen source pins and the original 138
registry count/ordered keys/hash. Independently approved K changes WILL fail this
historical gate. Retain and review the differences separately; do not bless them
by refreshing its baseline or silently report this gate passing.

The native runner never imports or invokes integration_preservation.py. Every
native run still captures/pins actual current source and runtime, checks source
and runtime before/after execution, and retains logs/cleanup. Historical baseline
pins neither replace that provenance nor restrict routine test maintenance.

Native results from the earlier private candidate (9 groups / 204 assertions)
are historical private evidence, not results on the current main core. The
portable runner/import and test-support changes require fresh post-integration
validation. No native test was run to prepare this package.

Arena rejection evidence is a closed forbidden-reference predicate theorem for
the next declaration plus an authenticated accepted prefix. It is NOT a closed
negative theorem for complete-file l4_safety_full or the old l4_input_valid.
