#!/bin/bash
# Read-only source/object audit. Reports are written only below toolchain/logs.
set -euo pipefail
ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$ROOT"
export LC_ALL=C

vernac='(^|[.][[:space:]])[[:space:]]*((Local|Global|Polymorphic|Monomorphic)[[:space:]]+)*(Admitted[[:space:]]*[.]|(Axioms?|Parameters?)[[:space:]]|Unset[[:space:]]+(Guard|Positivity|Universe|Elimination)[[:space:]]+Checking|Unset[[:space:]]+Extraction[[:space:]]+SafeImplicits|Extract[[:space:]]+(Constant|Inductive|Inlined[[:space:]]+Constant))'
tactics='(^|[;{}]|[.][[:space:]]+)[[:space:]]*admit[[:space:]]*([.;}]|$)|\b(vm_cast_no_check|native_cast_no_check|exact_no_check)\b|\bExtr(Ocaml|Haskell|Scheme)[[:alnum:]_]*\b'
ocaml='\b(new_axiom|mk_thm)\b|\bObj[[:space:]]*[.][[:space:]]*(magic|obj|set_field|set_tag|new_block|truncate)\b|\bMarshal[[:space:]]*[.][[:space:]]*from_(string|bytes|channel)\b'

is_generated() {
    case "$1" in
        rocq/lean_core.ml|rocq/lean_core.mli|rocq/lean_arena.ml|rocq/lean_arena.mli|\
        rocq/depth_native.ml|rocq/depth_native.mli|\
        rocq/metadata_native.ml|rocq/metadata_native.mli|\
        rocq/cheap_header_native.ml|rocq/cheap_header_native.mli|\
        rocq/persistent_tests_native.ml|rocq/persistent_tests_native.mli|\
        rocq/string_parity.ml|rocq/string_parity.mli|\
        rocq/environment_index_extracted.ml|rocq/environment_index_extracted.mli|\
        rocq/environment_index_suffix_extracted.ml|rocq/environment_index_suffix_extracted.mli|\
        rocq/eager_policy_native.ml|rocq/eager_policy_native.mli|\
        rocq/guard_order_native.ml|rocq/guard_order_native.mli|\
        rocq/whnf_policy_native.ml|rocq/whnf_policy_native.mli|\
        rocq/whnf_production_native.ml|rocq/whnf_production_native.mli|\
        rocq/universe_native.ml|rocq/universe_native.mli|\
        rocq/universe_complete_native.ml|rocq/universe_complete_native.mli|\
        rocq/universe_instantiation_native.ml|rocq/universe_instantiation_native.mli|\
        rocq/universe_expression_native.ml|rocq/universe_expression_native.mli) return 0 ;;
        *) return 1 ;;
    esac
}

if [[ ${1:-} == --self-test ]]; then
    positives=('Admitted.' 'Proof. admit.' 'Axiom bad : False.' 'Parameter trusted : nat.'
        'Unset Guard Checking.' 'Unset Positivity Checking.' 'Unset Universe Checking.'
        'Extract Constant bad => "unsafe".' 'Unset Extraction SafeImplicits.'
        'From Stdlib Require Import ExtrOcamlNatInt.'
        'exact_no_check proof.' 'let bad = new_axiom term;;' 'let x = Obj.magic y'
        'let x = Obj . obj y' 'let x = Marshal.from_string data 0')
    negatives=('Definition admit (n : nat) := n.' '| InputAxiom : name -> input_decl'
        'let x = Wire.Axiom data' 'let rule = new_inductive_definition term;;'
        'Extraction Language OCaml.' 'Theorem good : True. Proof. exact I. Qed.'
        '(* Exactly refining Declarations.admit. *)' 'Check Declarations.admit.')
    for sample in "${positives[@]}"; do
        printf '%s\n' "$sample" | rg -q -U -e "$vernac" -e "$tactics" -e "$ocaml" || {
            printf 'Missed unsafe fixture: %s\n' "$sample" >&2; exit 1;
        }
    done
    for sample in "${negatives[@]}"; do
        if printf '%s\n' "$sample" | rg -q -U -e "$vernac" -e "$tactics" -e "$ocaml"; then
            printf 'False positive on fixture: %s\n' "$sample" >&2; exit 1
        fi
    done
    for module in lean_core lean_arena depth_native metadata_native cheap_header_native \
        string_parity persistent_tests_native environment_index_extracted environment_index_suffix_extracted \
        eager_policy_native guard_order_native whnf_policy_native whnf_production_native \
        universe_native universe_complete_native universe_instantiation_native universe_expression_native; do
        for extension in ml mli; do
            file="rocq/$module.$extension"
            is_generated "$file" || { printf 'Missed generated file: %s\n' "$file" >&2; exit 1; }
        done
    done
    for file in rocq/Extract.v rocq/ArenaExtract.v rocq/NewInductive.v rocq/InductiveUtils.v \
        frontend/lean_arena.ml rocq/lean_arena.ml.other rocq/metadata_tests.ml \
        frontend/string_parity.ml rocq/cheap_header_native.ml.other \
        frontend/persistent_tests_native.ml rocq/PersistentTestsExtract.v; do
        if is_generated "$file"; then
            printf 'Incorrectly classified as generated: %s\n' "$file" >&2; exit 1
        fi
    done
    echo 'PASS: admission/cast scan and generated-file classification fixtures'
    exit 0
fi
[[ $# -eq 0 ]] || { echo 'Usage: audit-build.sh [--self-test]' >&2; exit 2; }
command -v rg >/dev/null
[[ ! -e toolchain/.setup-lock ]] || { echo 'Toolchain setup is active; retry after it finishes.' >&2; exit 1; }
grep -Fxq -- '-Q . LeanPort' rocq/_CoqProject || {
    echo 'Audit loadpath needs review: expected -Q . LeanPort in rocq/_CoqProject.' >&2; exit 1;
}
report="toolchain/logs/audit-$(date -u +%Y%m%dT%H%M%SZ)-$$"
mkdir -p "$report"
inventory() {
    find rocq hol frontend -type f \( -name '*.v' -o -name '*.vo' -o -name '*.ml' -o -name '*.mli' \) -print | sort
}
inventory > "$report/inventory-before.txt"
sources=(); handwritten=(); generated=(); vernacular=(); ml=(); objects=(); modules=()
while IFS= read -r file; do
    sources+=("$file")
    if is_generated "$file"; then
        generated+=("$file")
        continue
    fi
    handwritten+=("$file")
    case "$file" in
        *.v) vernacular+=("$file") ;;
        *.ml|*.mli) ml+=("$file") ;;
    esac
done < <(rg --files --hidden --no-ignore rocq hol frontend -g '*.v' -g '*.ml' -g '*.mli' | sort)
while IFS= read -r -d '' file; do
    objects+=("$file")
    module=${file#rocq/}; module=${module%.vo}; module=${module//\//.}
    modules+=("LeanPort.$module")
done < <(find rocq -type f -name '*.vo' -print0)
[[ ${#vernacular[@]} -gt 0 && ${#ml[@]} -gt 0 && ${#objects[@]} -gt 0 ]] || {
    echo 'Missing handwritten sources or Rocq objects; build the ports first.' >&2; exit 1;
}
printf '%s\n' "${handwritten[@]}" > "$report/handwritten-files.txt"
if [[ ${#generated[@]} -gt 0 ]]; then
    printf '%s\n' "${generated[@]}" > "$report/generated-files.txt"
else
    : > "$report/generated-files.txt"
fi
printf '%s\n' "${modules[@]}" > "$report/checked-modules.txt"
shasum -a 256 "${sources[@]}" "${objects[@]}" > "$report/inputs.sha256"
status=0
for file in "${vernacular[@]}"; do
    object=${file%.v}.vo
    if [[ ! -f "$object" || "$file" -nt "$object" ]]; then
        printf 'MISSING/STALE: %s (source %s)\n' "$object" "$file" | tee -a "$report/stale-objects.txt"
        status=1
    fi
done
scan() {
    local output=$1 result=0
    shift
    rg -n -U --color never "$@" > "$output" || result=$?
    if [[ $result -eq 0 ]]; then
        cat "$output"
        status=1
    elif [[ $result -ne 1 ]]; then
        echo "Scanner error ($result): $output" >&2
        status=1
    fi
}
scan "$report/rocq-scan.txt" -e "$vernac" -e "$tactics" -- "${vernacular[@]}"
scan "$report/ocaml-hol-scan.txt" -e "$ocaml" -- "${ml[@]}"
# Generated extraction is reported separately, never silently treated as handwritten.
if [[ ${#generated[@]} -gt 0 ]]; then
    scan "$report/generated-extraction-scan.txt" -e "$ocaml" -- "${generated[@]}"
fi
sh scripts/toolchain-exec.sh rocq --version > "$report/rocq-version.txt"
kernel_status=PASS
if ! sh scripts/toolchain-exec.sh rocq check -Q rocq LeanPort -o "${modules[@]}" > "$report/rocq-check.log" 2>&1; then
    tail -60 "$report/rocq-check.log"
    kernel_status=FAIL
    status=1
fi
for expected in '* Axioms: <none>' \
    '* Constants/Inductives relying on type-in-type: <none>' \
    '* Constants/Inductives relying on unsafe (co)fixpoints: <none>' \
    '* Inductives whose positivity is assumed: <none>'; do
    if ! grep -Fxq -- "$expected" "$report/rocq-check.log"; then
        printf 'Assumption summary needs review: expected %s\n' "$expected" >&2
        status=1
    fi
done
shasum -a 256 "${sources[@]}" "${objects[@]}" > "$report/inputs-after.sha256"
if ! cmp -s "$report/inputs.sha256" "$report/inputs-after.sha256"; then
    echo 'Sources/objects changed during audit; rebuild and rerun on a stable tree.' >&2
    status=1
fi
inventory > "$report/inventory-after.txt"
if ! cmp -s "$report/inventory-before.txt" "$report/inventory-after.txt"; then
    echo 'Source/object inventory changed during audit; rerun on a stable tree.' >&2
    status=1
fi
printf 'Audit report: %s\nRocq objects selected: %s\nKernel recheck: %s\n' "$report" "${#objects[@]}" "$kernel_status"
if [[ $status -eq 0 ]]; then
    echo 'PASS: object recheck and conservative source scan; NOT whole-checker verification.'
else
    echo 'FAIL: review the report; no whole-checker verification claim.' >&2
fi
exit "$status"
