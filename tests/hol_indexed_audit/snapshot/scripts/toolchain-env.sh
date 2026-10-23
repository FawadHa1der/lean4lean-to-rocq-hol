#!/bin/sh
# Source only from a script that has set PROJECT_ROOT to the physical root.
: "${PROJECT_ROOT:?PROJECT_ROOT must be set}"
TOOLCHAIN_DIR="$PROJECT_ROOT/toolchain"
toolchain_hash=$(printf '%s' "$TOOLCHAIN_DIR" | shasum -a 256 | cut -c 1-12)
TOOLCHAIN_ALIAS="/private/tmp/lean4lean-$(id -u)-$toolchain_hash"
if [ -L "$TOOLCHAIN_ALIAS" ]; then
    [ "$(readlink "$TOOLCHAIN_ALIAS")" = "$TOOLCHAIN_DIR" ] || {
        echo "Refusing mismatched toolchain alias: $TOOLCHAIN_ALIAS" >&2
        return 1
    }
elif [ -e "$TOOLCHAIN_ALIAS" ]; then
    if [ ! -L "$TOOLCHAIN_DIR" ] || [ "$(readlink "$TOOLCHAIN_DIR")" != "$TOOLCHAIN_ALIAS" ]; then
        echo "Refusing occupied toolchain alias: $TOOLCHAIN_ALIAS" >&2
        return 1
    fi
else
    ln -s "$TOOLCHAIN_DIR" "$TOOLCHAIN_ALIAS"
fi
export OPAMROOT="$TOOLCHAIN_ALIAS/opam-root"
export OPAMSWITCH=lean4lean
export OPAMYES=1
export OPAMJOBS="${TOOLCHAIN_JOBS:-4}"
export OPAMNODEPEXTS=true
export OPAMNOENVNOTICE=true
unset OPAMCLI
export PATH="$TOOLCHAIN_ALIAS/bin:$OPAMROOT/$OPAMSWITCH/bin:$PATH"
export OCAMLLIB="$OPAMROOT/$OPAMSWITCH/lib/ocaml"
export CAML_LD_LIBRARY_PATH="$OPAMROOT/$OPAMSWITCH/lib/stublibs:$OCAMLLIB/stublibs"
export OCAML_TOPLEVEL_PATH="$OPAMROOT/$OPAMSWITCH/lib/toplevel"
export PERL5LIB="$TOOLCHAIN_ALIAS/perl5/lib/perl5${PERL5LIB:+:$PERL5LIB}"
if [ -d /opt/homebrew/opt/gmp ]; then
    export CPATH="/opt/homebrew/opt/gmp/include${CPATH:+:$CPATH}"
    export LIBRARY_PATH="/opt/homebrew/opt/gmp/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
    export PKG_CONFIG_PATH="/opt/homebrew/opt/gmp/lib/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}"
fi
export TOOLCHAIN_DIR TOOLCHAIN_ALIAS
