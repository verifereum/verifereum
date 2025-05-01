open HolKernel boolLib bossLib cv_transLib
     vfmStateTestDefs10Theory
     vfmTestLib Timeout

val () = new_theory "vfmStateTests";

fun get_result_defs thyn =
  thyn |> definitions |> List.filter (String.isSuffix "result_def" o #1);

fun trimr n = Substring.string o Substring.trimr n o Substring.full;

val eval_rhs = CONV_RULE $ RAND_CONV cv_eval;

fun prove_result_thm limit (result_def_name, result_def) = let
  val result_name = trimr 4 result_def_name
  val () = Feedback.HOL_MESG $ String.concat ["Evaluating ", result_name]
  val start_time = Time.now()
  val result_eval = Timeout.apply limit eval_rhs result_def
  val end_time = Time.now()
  val () = Feedback.HOL_MESG $ String.concat $ [
             thm_to_string result_eval,
             " (", Time.fmt 2 $ end_time - start_time, "s)"
           ]
in
  ignore $ save_thm(result_name, result_eval)
end

val limit = Time.fromSeconds 120;

val thyn = "vfmStateTestDefs10";

val result_defs = get_result_defs thyn;

val () = List.app (prove_result_thm limit) result_defs;

val () = export_theory_no_docs ();
