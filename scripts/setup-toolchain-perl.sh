#!/bin/sh
set -eu
PROJECT_ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd -P)
. "$PROJECT_ROOT/scripts/toolchain-env.sh"
if /usr/bin/perl -MString::ShellQuote -e 1 2>/dev/null; then
    exit 0
fi
archive="$TOOLCHAIN_DIR/downloads/String-ShellQuote-1.04.tar.gz"
mkdir -p "$TOOLCHAIN_DIR/downloads"
if [ ! -f "$archive" ]; then
    curl -fL --retry 3 https://cpan.metacpan.org/authors/id/R/RO/ROSCH/String-ShellQuote-1.04.tar.gz -o "$archive"
fi
actual=$(shasum -a 256 "$archive" | cut -d ' ' -f 1)
[ "$actual" = e606365038ce20d646d255c805effdd32f86475f18d43ca75455b00e4d86dd35 ] || {
    echo "String::ShellQuote checksum mismatch" >&2
    exit 1
}
tar -xzf "$archive" -C "$TOOLCHAIN_DIR/downloads"
cd "$TOOLCHAIN_ALIAS/downloads/String-ShellQuote-1.04"
/usr/bin/perl Makefile.PL INSTALL_BASE="$TOOLCHAIN_ALIAS/perl5"
make
PERL5LIB="$TOOLCHAIN_ALIAS/downloads/String-ShellQuote-1.04/blib/lib:$PERL5LIB" make test
make install
/usr/bin/perl -MString::ShellQuote -e 1
