(* Pure OCaml allocation tests; no HOL startup or theorem verdicts. *)
open Shift_left_budget;;
module B=Lean4hol_shift_left_budget;;
let count=ref 0;;
let check label p=if not p then failwith label else incr count;;
let allowed bits left shift=B.check ~max_output_bits:bits left shift=B.Allowed;;
let resource bits left shift=match B.check ~max_output_bits:bits left shift with B.Exhausted _->true|_->false;;
let invalid bits left shift=match B.check ~max_output_bits:bits left shift with B.Invalid _->true|_->false;;
List.iter(fun(left,shift)->check "modest or large allowed" (allowed 4096 left shift))
  ["0","0";"13","7";"1","256";"9876543210987654321098765432109876543210","64";
   "0",String.make 1000 '9'];;
check "huge positive shift declined" (resource 4096 "1" (String.make 1000 '9'));;
check "hard decimal cap before arithmetic" (resource 4096 "0" (String.make 16385 '9'));;
check "hard budget cap" (invalid max_int "1" "1");;
List.iter(fun x->check "invalid decimal" (invalid 4096 x "0")) ["";"00";"-1";"1x";"1.0"];;
List.iter(fun bad->
  check "malformed left not canonical" (not(B.canonical bad));
  check "malformed left classified invalid" (invalid 4096 bad "0");
  check "malformed shift classified invalid" (invalid 4096 "1" bad);
  check "zero never bypasses decimal validation" (invalid 4096 "0" bad))
  ["";"00";"01";"-0";"-1";"+1";" 1";"1 ";"1\n";"1.0";"1e3";"0x10";"1x"];;
List.iter(fun good->check "canonical decimal accepted" (B.canonical good))
  ["0";"1";"10";"100";"9999999999999999999999999999999999999999"];;
check "zero with enormous exponent and one-bit cap allowed" (allowed 1 "0" (String.make 1000 '9'));;
check "zero with hard-limit exponent text allowed" (allowed 1 "0" (String.make 16384 '9'));;
check "nonzero with same enormous exponent declined" (resource 1 "1" (String.make 1000 '9'));;
check "one-bit exact result conservatively declined" (resource 1 "1" "0");;
check "two-bit exact result conservatively declined" (resource 4 "1" "1");;
check "same positive result allowed by larger preflight" (allowed 5 "1" "1");;
check "zero output budget invalid" (invalid 0 "0" "0");;
check "negative output budget invalid" (invalid (-1) "0" "0");;
check "preflight only sees operands, not any claimed answer" (allowed 4096 "13" "7");;
(* Exhaustive small machine-integer check of the conservative output bound. *)
for bits=4 to 30 do
  for value=1 to 127 do
    for shift=0 to 26 do
      if allowed bits (string_of_int value) (string_of_int shift) then
        check "allowed nonzero result strictly below bit ceiling"
          ((value lsl shift)<(1 lsl bits))
    done
  done
done;;
for bits=4 to 512 do
  for digits=1 to 32 do
    let left=String.make digits '9' in
    if 4*digits<=bits then begin
      check "conservative bound inclusive" (allowed bits left(string_of_int(bits-4*digits)));
      check "one extra output bit declined" (resource bits left(string_of_int(bits-4*digits+1)))
    end else check "input alone exceeds bound" (resource bits left "0")
  done
done;;
Printf.printf "SHIFT_LEFT_BUDGET_OFFLINE_PASSED %d\n%!" !count;;
