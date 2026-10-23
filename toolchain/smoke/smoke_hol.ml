let toolchain_smoke_thm = prove (`!n:num. n + 0 = n`, ARITH_TAC);;
let toolchain_rejects_false =
  try ignore(prove (`F`, REWRITE_TAC[])); false with Failure _ -> true;;
if hyp toolchain_smoke_thm = [] &&
   concl toolchain_smoke_thm = `!n:num. n + 0 = n` &&
   toolchain_rejects_false
then (print_endline "HOL_THEOREM_AND_REJECTION_OK"; exit 0)
else exit 1;;
