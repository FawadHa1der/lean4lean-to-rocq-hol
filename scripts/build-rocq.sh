#!/bin/sh
set -eu
PROJECT_ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$PROJECT_ROOT"
sh scripts/build-frontend.sh
mkdir -p build/rocq
run() { sh "$PROJECT_ROOT/scripts/toolchain-exec.sh" "$@"; }
(
    cd rocq
    # Rebuild every local proof and regression root in dependency order.
    # All extraction commands run here, so their generated paths are stable.
    for source in ./*.v; do
        case "$source" in
            *[!a-zA-Z0-9_./]*) echo "Unsupported Rocq source name: $source" >&2; exit 1 ;;
        esac
    done
    order=$(run rocq dep -sort -Q . LeanPort ./*.v)
    [ -n "$order" ] || { echo 'No Rocq modules found.' >&2; exit 1; }
    for source in $order; do
        run rocq compile -Q . LeanPort "$source"
    done
)
sh scripts/link-rocq.sh
python3 scripts/test_rocq_native.py
