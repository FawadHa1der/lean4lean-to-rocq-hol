# Project-Local Toolchains

This setup builds OCaml, Rocq and HOL Light independently of Lean and Solidity.
It does not modify shell profiles, `~/.opam`, or Homebrew, and does not install
system packages. All persistent toolchain artifacts belong under `toolchain/`.

## Pinned Inputs

| Component | Version |
| --- | --- |
| opam binary | 2.6.0, Darwin arm64 |
| OCaml | 4.14.2 |
| Rocq core/runtime | 9.2.0 |
| Rocq Stdlib | 9.1.0 |
| Rocq metapackage | `rocq-prover.meta.1` |
| HOL Light | 3.1.0 |
| Yojson | 3.0.0 |
| Zarith | 1.14 |
| String::ShellQuote (Perl build dependency) | 1.04 |

The opam repository is fixed at
`ec0f6516081487aab3b181feb1d7f169c32e6fb1`. Package source checksums come from
that snapshot. The opam binary and Perl archive have SHA-256 checks in the
setup scripts. `toolchain/switch.export` records the resolved dependency
closure and full package metadata after installation; subsequent setup runs
import it. `toolchain/installed-packages.txt` records installed versions.
This is source/package reproducibility, not a bit-for-bit reproducible binary
claim or a fully hermetic build.

## Prerequisites

The bootstrap currently supports macOS arm64 only. It needs Xcode command-line
build tools, `make`, `git`, `curl`, `shasum`, `tar`, Perl, and an existing GMP
development installation. On this host, GMP is read from
`/opt/homebrew/opt/gmp`; setup does not run `brew install`.
String::ShellQuote is built and tested under `toolchain/perl5` when missing.
Other missing external dependencies cause a build failure instead of a global
package install. Initial setup needs network access to GitHub, opam's source
mirrors, and CPAN; routine compiler use and smoke tests do not need network.

On macOS 26.6.2 with Apple clang 21, the SDK advertises weak `pipe2` and `dup3`
symbols absent at runtime. An initial OCaml build consequently crashed in
`Unix.pipe` while building dependencies. Setup sets the Autoconf cache values
`ac_cv_func_pipe2=no` and `ac_cv_func_dup3=no` to select OCaml's portable
implementations, and recompiles a prior broken compiler and its dependents.
These are OS feature selections, not relaxed proof checks. The smoke test
exercises Unix pipes and close-on-exec descriptor duplication.

## Setup and Use

From the project root:

```sh
sh scripts/setup-toolchains.sh
sh scripts/toolchain-exec.sh ocamlc -version
sh scripts/toolchain-exec.sh rocq --version
sh scripts/toolchain-exec.sh ocamlfind query yojson zarith
sh scripts/toolchain-smoke.sh
```

Set `TOOLCHAIN_JOBS=2` before setup to reduce parallel build load (default 4).
Setup is resumable and preserves partial installs. Do not run two setup
processes concurrently, or compile against this toolchain while setup moves
its storage. A setup lock prevents concurrent setup runs.

Use `sh scripts/toolchain-exec.sh COMMAND ARG...` for every integration command.
It injects only process-local paths and preserves the caller's working
directory and argument boundaries. Examples:

```sh
sh scripts/toolchain-exec.sh rocq compile path/to/File.v
sh scripts/toolchain-exec.sh ocamlfind ocamlopt -package yojson,zarith -linkpkg example.ml -o example
LINE_EDITOR=env sh scripts/toolchain-exec.sh hol.sh < proof.ml > hol-run.log 2>&1
```

This switch provides `rocq compile`, not a legacy `coqc` executable. Use the
former in build scripts instead of assuming a compatibility alias exists.

HOL Light's REPL may return exit code zero after a load or parse error. Batch
callers must check a success marker produced after the final theorem and scan
for errors, as `toolchain-smoke.sh` does. The launcher does not forward general
command-line arguments to OCaml; stdin is the supported batch input here.

## Paths and Spaces

For this checkout the runtime prefix is:

```text
/private/tmp/lean4lean-501-e16fccc9822d/opam-root/lean4lean
```

Its persistent backing directory is:

```text
/Users/fawadhaider/code/lean4 in rocq:hol light/toolchain/opam-root/lean4lean
```

Executables are under `bin/`; HOL Light sources and `ocaml-hol` are under
`lib/hol_light/`; OCaml libraries are under `lib/`.
The local opam executable is `toolchain/bin/opam`.

OCaml/opam/HOL Light build scripts do not consistently handle spaces, and a
colon also conflicts with OCaml library search-path syntax. Opam resolves
symlinks, so an ordinary symlink is insufficient during compilation. Setup
temporarily moves the `toolchain/` tree to a unique, physical, space-free
`/private/tmp/lean4lean-UID-HASH` directory and leaves a project-side symlink.
On normal completion or handled failure it moves the complete tree back,
leaving only a temporary-directory symlink into the project. The wrapper
recreates that alias after reboot. It intentionally avoids `opam exec`, which
would canonicalize paths back to the colon-containing project name.

Source snapshots usually symlink `toolchain/` to the existing installation.
The launcher resolves that link before deriving the alias, so it can restore
the installation's compiled prefix even if its temporary alias disappeared.
Setup's deliberate temporary relocation is preserved. Conflicting aliases and
occupied paths are refused rather than overwritten. Eight isolated regression
tests cover these cases:

```sh
python3 -B -m unittest discover -s tests/toolchain -p test_alias.py -v
```

Do not move this checkout without rebuilding the toolchain: compiled prefixes
include the alias derived from its physical path and user id. Do not run raw
`opam install` at rest; use the setup script so compilation uses staging.
After an uncatchable interruption, confirm no setup process remains, remove
only the empty `toolchain/.setup-lock` directory, then rerun setup; it detects
and resumes the staged layout. All source/build caches and upstream licenses
remain local. Generated directories are ignored by `toolchain/.gitignore`.

## Smoke Coverage and Trust

`toolchain-smoke.sh` checks:

- Rocq compiles a proved arithmetic theorem and reports no extra assumptions.
- `rocq check` independently rechecks the resulting object.
- An intentionally invalid proof is rejected with a type error.
- Rocq extracts a successor function; native OCaml compiles and runs it.
- Yojson parses JSON and Zarith checks a 101-bit integer in that executable.
- HOL Light constructs a closed arithmetic theorem and fails to prove `F`.
- HOL Light's initialization and user input contain no reported errors.

Logs are in `toolchain/logs/`, and smoke build products in
`toolchain/smoke-build/`. These are toolchain checks, not proofs of correctness
for either port. The extraction smoke uses machine-integer naturals only on a
small bounded input; it is not a claim that this mapping preserves unbounded
natural-number arithmetic. HOL Light loads its normal upstream core; the
optional `hol_light_module` inliner/module build is not enabled. No new project
axioms, admitted proofs, or disabled logical checking flags are introduced.

## Verified Status

Verified on 2026-09-29: the complete `sh scripts/toolchain-smoke.sh` passed on
macOS 26.6.2 arm64 with Apple clang 21.0.0. Setup has finished, the persistent
tree is back under the project, and compiler use is safe. The normal upstream
HOL initialization emits warnings; the smoke log contains the final theorem
and rejection marker with no reported errors. See `TRUST_AUDIT.md` for the
separate port-object/source audit and its limitations.

## Official References

- [opam installation](https://opam.ocaml.org/doc/Install.html)
- [opam 2.6.0 release](https://github.com/ocaml/opam/releases/tag/2.6.0)
- [Rocq opam installation](https://rocq-prover.org/docs/using-opam)
- [Rocq runtime package](https://opam.ocaml.org/packages/rocq-runtime/rocq-runtime.9.2.0/)
- [HOL Light 3.1.0 README](https://github.com/jrh13/hol-light/blob/Release-3.1.0/README)
- [HOL Light 3.1.0 build and module trust note](https://github.com/jrh13/hol-light/blob/Release-3.1.0/Makefile)
