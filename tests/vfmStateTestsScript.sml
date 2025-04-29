open HolKernel boolLib bossLib cv_transLib
     vfmStateTestDefs100Theory vfmTestLib

val () = new_theory "vfmStateTests";

val result_defs = "vfmStateTestDefs100"
  |> definitions |> List.filter (String.isSuffix "result_def" o #1)

val (_, result_def) = el 1 result_defs
val result_eval = cv_eval (rhs (concl result_def))

val () = export_theory_no_docs ();
