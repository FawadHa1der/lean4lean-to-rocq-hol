#!/bin/sh
# Private direct-child launcher so the timed supervisor reaps HOL itself.
set -eu
PROJECT_ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$PROJECT_ROOT"
. "$PROJECT_ROOT/scripts/toolchain-env.sh"
HOLLIGHT_DIR=$(hol.sh -dir)
export HOLLIGHT_DIR
export HOLLIGHT_USE_MODULE=0
exec "$HOLLIGHT_DIR/ocaml-hol" -init "$HOLLIGHT_DIR/hol.ml" -I "$HOLLIGHT_DIR"
