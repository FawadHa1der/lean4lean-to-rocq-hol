# Primitive Contract Regressions

These commands run native HOL Light proof construction. Each phase retains a
full log, exact source hashes, a completion marker and a JSON result. Timeout,
HOL errors, source changes or missing markers fail the phase; the child process
group is killed and reaped. Negative proof-search declines are not refutations.

```sh
python3 tests/hol_primitives/run_contract.py shift-left --phase checks
python3 tests/hol_primitives/run_contract.py shift-left --phase equations --timeout 300
python3 tests/hol_primitives/run_contract.py shift-left --phase body
python3 tests/hol_primitives/run_contract.py shift-left --phase named
python3 tests/hol_primitives/run_contract.py shift-left --phase base
python3 tests/hol_primitives/run_contract.py shift-left --phase step
python3 tests/hol_primitives/run_contract.py shift-left --phase order
python3 tests/hol_primitives/run_contract.py shift-left --phase output
python3 tests/hol_primitives/run_contract.py shift-left --phase replay
python3 tests/hol_primitives/run_contract.py shift-left --phase missing
python3 tests/hol_primitives/run_contract.py pow --phase factory
python3 tests/hol_primitives/run_contract.py admission
```

The original `shift-left --phase factory` retains all checks in one run. The
`checks` and `equations` phases split that same set, each keeping the complete
positive admission setup. Repeated setup assertions are not distinct tests.
The split does not change the validator, symbolic equations or adversarial
requirements. An earlier unsplit integration attempt exhausted its 180s wall cap.

For the general file frontend, start the private worker with a sufficient
per-case cap, retain its startup provenance, then run:

```sh
python3 tests/hol_primitives/test_exports.py --socket /private/tmp/hol-run-EXAMPLE/s --timeout 180
```

The three generated fixtures require actual admission of canonical Nat plus
symbolically validated add/mul/shiftLeft definitions, a dependent-type conversion
checking `shiftLeft 1 1 = 2`, and a wrong-result control. The positive admission
gate must pass before any other case runs. Timeout on a negative does not count
as its expected decline. These are generated controls, not extra Arena cases.
