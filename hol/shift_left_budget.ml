(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Allocation preflight only; this module cannot produce a logical verdict. *)
module Lean4hol_shift_left_budget = struct
  type decision = Allowed | Invalid of string | Exhausted of string
  let canonical s =
    let n=String.length s in
    n>0 && (n=1 || s.[0]<>'0') &&
    let ok=ref true in
    String.iter(fun c->if c<'0' || c>'9' then ok:=false)s;
    !ok
  let check ~max_output_bits left shift =
    if max_output_bits<1 || max_output_bits>65536 then
      Invalid "max_output_bits must be between 1 and 65536"
    else if String.length left>16384 || String.length shift>16384 then
      Exhausted "shiftLeft decimal input length cap"
    else if not(canonical left && canonical shift) then
      Invalid "shiftLeft operands must be canonical nonnegative decimal"
    else if left="0" then Allowed
    else if String.length left>max_output_bits/4 then
      Exhausted "shiftLeft conservative input bit bound"
    else
      let remaining=max_output_bits-4*String.length left in
      let bound=string_of_int remaining in
      if String.length shift>String.length bound ||
         (String.length shift=String.length bound && String.compare shift bound>0) then
        Exhausted "shiftLeft conservative output bit bound"
      else Allowed
end;;
