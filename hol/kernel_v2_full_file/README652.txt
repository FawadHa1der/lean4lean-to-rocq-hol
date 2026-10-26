Full-file HOL candidate652 - SOURCE ONLY / UNCOMPILED
===================================================
This candidate assembles the actual full-syntax checker, admission, file
boundary and computation sources from reviewed checkpoints639/651 and610.
It preserves every previous637 project source, including proposed proofs.
It is NOT the default checker, a compiled proof result or an Arena submission.

All project imports point into hol/ within this candidate. The required stock
dependency source files are copied byte-for-byte with their original license.
MANIFEST652.json records original, archived/read source and output identities,
every literal needs relocation and the two fixture I/O adaptations. Original
source/evidence remains unchanged. The source-package notices/licenses and
candidate documents are selected in a separately sealed metadata inventory;
no metadata is rediscovered during copying. Relative lookup requires the outer runner
to pin cwd to this candidate and load_path to exactly[candidate cwd]. No extra
temporary-directory fallback is intended. The normal pinned stock HOL bootstrap
and external genuine Wire/Replay/Zarith/Yojson loading remain separate reviewed
requirements; this source bundle does not authenticate them or their ABI.

Held entry sources655 select actual proof or test work. Merely copying them
does not execute them or authorize a new session. Loading HOL sources can
construct definitions, datatype facts and proposed proofs; it is not a promise
of no loading work. Each actual run needs the existing fresh resource/ownership/
deadline/cleanup gates and the selected stage's complete source/host custody.
Any first resource/ownership/cleanup failure remains fatal under that session.

Fixture changes only:
641 requires LEAN4LEAN_FIXTURE_TMPDIR to name an absolute scratch directory
owned/validated by the outer job. There is no default scratch fallback; relative
or absent values fail. It no longer writes into its source package. This local
path check alone does NOT establish directory ownership or confinement.
649's static six NDJSON fixtures live in fixtures/649 relative to the pinned
candidate cwd. Checker definitions, expected outcomes and input bytes are not
changed by these I/O adaptations. All such tests remain UNRUN.

The actual647 registry and its explicit stock conversion list remain mandatory.
Do not insert expected fixture outcome theorems into it. Unknown computation
must remain inconclusive, not rejected or accepted. HOL computed equalities
are distinct from whole-Lean semantic correctness, input authenticity and truth
of admitted source axioms. No trust/resource requirement is weakened here.

Still required: actual parsing/proof construction/closed computations, host
integration, audited source/runtime custody, default CLI integration after real
validation, fresh Rocq integration/audit/extraction and complete234-case pinned
Arena accounting for both ports. No Solidity edits, commits, pushes or publication.
