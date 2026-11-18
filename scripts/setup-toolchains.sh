#!/bin/sh
set -eu
PROJECT_ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd -P)
mkdir -p "$PROJECT_ROOT/toolchain/bin" "$PROJECT_ROOT/toolchain/logs" "$PROJECT_ROOT/toolchain/downloads"
. "$PROJECT_ROOT/scripts/toolchain-env.sh"
case "$(uname -s)/$(uname -m)" in
    Darwin/arm64)
        opam_asset=opam-2.6.0-arm64-macos
        opam_sha=b57ed6cc082e560063989a285c59786b7c670087da2d317a87e4ba4c7973e71f
        ;;
    Linux/x86_64)
        # Digest published by GitHub for the 2.6.0 release asset.
        opam_asset=opam-2.6.0-x86_64-linux
        opam_sha=a59184447f881005dae70b2ae455c3a7e9549834a41c635c49a5a28235eca758
        ;;
    *)
        echo "This bootstrap pins opam binaries for Darwin/arm64 and Linux/x86_64 only." >&2
        exit 1
        ;;
esac
if ! mkdir "$TOOLCHAIN_DIR/.setup-lock" 2>/dev/null; then
    echo "Another setup may be running; inspect toolchain/.setup-lock before retrying." >&2
    exit 1
fi
# opam canonicalizes symlinks, so builds need a physical space-free directory.
# At rest the complete tree is inside the project; only this alias is in /tmp.
if [ -L "$TOOLCHAIN_ALIAS" ]; then
    unlink "$TOOLCHAIN_ALIAS"
    mv "$TOOLCHAIN_DIR" "$TOOLCHAIN_ALIAS"
    ln -s "$TOOLCHAIN_ALIAS" "$TOOLCHAIN_DIR"
fi
restore_toolchain() {
    if [ -L "$TOOLCHAIN_DIR" ] && [ "$(readlink "$TOOLCHAIN_DIR")" = "$TOOLCHAIN_ALIAS" ]; then
        unlink "$TOOLCHAIN_DIR"
        mv "$TOOLCHAIN_ALIAS" "$TOOLCHAIN_DIR"
        ln -s "$TOOLCHAIN_DIR" "$TOOLCHAIN_ALIAS"
    fi
}
finish_setup() {
    restore_toolchain
    rmdir "$TOOLCHAIN_DIR/.setup-lock"
}
trap finish_setup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
unset OCAMLLIB CAML_LD_LIBRARY_PATH OCAML_TOPLEVEL_PATH
if [ "$(uname -s)" = Darwin ]; then
    # The host SDK weak-links these symbols, but this macOS runtime lacks them.
    # Select OCaml's portable pipe/fcntl and dup2/fcntl implementations instead.
    export ac_cv_func_pipe2=no
    export ac_cv_func_dup3=no
fi
opam="$TOOLCHAIN_ALIAS/bin/opam"
opam_run() { "$opam" --cli=2.1 "$@"; }
if [ ! -f "$opam" ]; then
    curl -fL --retry 3 "https://github.com/ocaml/opam/releases/download/2.6.0/$opam_asset" -o "$opam.download"
    actual=$(toolchain_sha256 "$opam.download" | cut -d ' ' -f 1)
    [ "$actual" = "$opam_sha" ] || { echo "opam checksum mismatch" >&2; exit 1; }
    mv "$opam.download" "$opam"
    chmod +x "$opam"
fi
actual=$(toolchain_sha256 "$opam" | cut -d ' ' -f 1)
[ "$actual" = "$opam_sha" ] || { echo "opam checksum mismatch" >&2; exit 1; }
repository=git+https://github.com/ocaml/opam-repository.git#ec0f6516081487aab3b181feb1d7f169c32e6fb1
if [ ! -f "$OPAMROOT/config" ]; then
    # Linux sandboxes builds with bubblewrap, which unprivileged containers
    # often cannot provide; builds remain confined to the project prefix.
    sandbox_flag=
    if [ "$(uname -s)" = Linux ] && ! command -v bwrap >/dev/null 2>&1; then
        sandbox_flag=--disable-sandboxing
    fi
    opam_run init --root="$OPAMROOT" --bare --no-setup --shell=sh --yes $sandbox_flag default "$repository"
fi
sh "$PROJECT_ROOT/scripts/setup-toolchain-perl.sh"
if ! opam_run switch list --short | grep -qx "$OPAMSWITCH"; then
    opam_run switch create "$OPAMSWITCH" ocaml-base-compiler.4.14.2 --yes
fi
if nm -m "$OPAMROOT/$OPAMSWITCH/bin/ocamlbuild" 2>/dev/null | grep -Eq 'weak external _(pipe2|dup3) '; then
    opam_run reinstall --yes --no-depexts ocaml-base-compiler.4.14.2
fi
# switch.export records the macOS-resolved closure; on other hosts the pinned
# repository snapshot resolves the same package versions directly.
if [ "$(uname -s)" = Darwin ] && [ -f "$TOOLCHAIN_DIR/switch.export" ]; then
    opam_run switch import "$TOOLCHAIN_DIR/switch.export" --yes
fi
opam_run install --yes --no-depexts ocaml-base-compiler.4.14.2 rocq-prover.meta.1 rocq-core.9.2.0 rocq-stdlib.9.1.0 yojson.3.0.0 zarith.1.14 hol_light.3.1.0
if [ "$(uname -s)" = Darwin ]; then
    opam_run switch export --full "$TOOLCHAIN_DIR/switch.export"
fi
opam_run list --installed --columns=name,version > "$TOOLCHAIN_DIR/installed-packages.$(uname -s).txt"
if [ "$(uname -s)" = Darwin ]; then
    cp "$TOOLCHAIN_DIR/installed-packages.$(uname -s).txt" "$TOOLCHAIN_DIR/installed-packages.txt"
fi
printf 'Toolchain prefix: %s\n' "$OPAMROOT/$OPAMSWITCH"
restore_toolchain
sh "$PROJECT_ROOT/scripts/toolchain-smoke.sh"
