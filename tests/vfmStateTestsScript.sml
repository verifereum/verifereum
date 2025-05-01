open HolKernel boolLib bossLib cv_transLib
     vfmStateTestDefs100Theory vfmTestLib

val () = new_theory "vfmStateTests";

val result_defs = "vfmStateTestDefs100"
  |> definitions |> List.filter (String.isSuffix "result_def" o #1);

(* TODO: add timing and timeouts *)
val result_thms = List.map (I ## CONV_RULE (RAND_CONV cv_eval)) result_defs;

val () = List.app (fn (result_name, thm) =>
           ignore $ save_thm(
             Substring.string (Substring.trimr 4 (Substring.full result_name)),
             thm)) result_thms

val () = export_theory_no_docs ();
