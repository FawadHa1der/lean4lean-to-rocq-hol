#!/bin/sh
# Copyright (c) 2026 Fawad Haider. All rights reserved.
set -eu
PROJECT_ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$PROJECT_ROOT"
exec sh scripts/toolchain-exec.sh python3 scripts/hol-check.py --serve "$@"
