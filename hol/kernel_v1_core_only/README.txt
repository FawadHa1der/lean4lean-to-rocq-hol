Full-syntax HOL core candidate612: SOURCE ONLY / UNCOMPILED
========================================================
This candidate moves the reviewed core source out of temporary-path imports.
It is NOT the project's default checker and has NOT been run by HOL Light.

43 source files from the pinned605 graph are copied with only literal needs
paths rewritten into this bundle's hol/ directory. The two additional stock
HOL libraries are copied byte-for-byte with their license. Each rewrite and
original/output hash is recorded in MANIFEST612.json. All older sources remain
unchanged. Per-module NOTICE files preserve their original provenance and limits.

run_proofs612.ml is a held proof-entry proposal. It requires a reviewed, newly
authorized guarded stock-HOL process whose cwd and source bytes are bound to
this candidate. It fixes source lookup to that cwd; no earlier temporary source
root or alternate Library fallback is part of the proposal. Stock bootstrap,
host, parser, library cache, source custody and cleanup still need validation.
Do not treat this source package or marker strings as an execution authorization.

The10 direct proof entry files contain201 newly proposed scripts; transitive
sources also contain earlier scripts and standard HOL library proofs.201 is not
the total number of prover operations. None was newly checked by this packaging.
Successful future source loading alone would not establish Lean soundness or
environment admission, faithful file quotation, extraction or Arena outcomes.

Outstanding: source review of packaging/entry and actual guarded execution;
full declaration/inductive/nested/primitive/safety admission; input refinement;
Rocq integration; semantic proofs and complete current/pinned Arena validation.
No Solidity changes, publication, native execution or safeguard changes.
