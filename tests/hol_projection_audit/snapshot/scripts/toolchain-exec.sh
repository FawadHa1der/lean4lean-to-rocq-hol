#!/bin/sh
set -eu
PROJECT_ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd -P)
. "$PROJECT_ROOT/scripts/toolchain-env.sh"
[ -x "$TOOLCHAIN_ALIAS/bin/opam" ] || {
    echo "Run sh scripts/setup-toolchains.sh first." >&2
    exit 1
}
# opam exec canonicalizes the prefix, reintroducing the colon into OCaml paths.
exec "$@"
