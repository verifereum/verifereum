open HolKernel boolLib bossLib cv_transLib
     vfmStateTestDefs10Theory
     vfmTestLib Timeout

val () = new_theory "vfmStateTests";

fun get_result_defs thyn =
  thyn |> definitions |> List.filter (String.isSuffix "result_def" o #1);

fun trimr n = Substring.string o Substring.trimr n o Substring.full

fun prove_result_thm limit thyn (result_def_name, result_def) = let
  val result_name = trimr 4 result_def_name
  val exec_def_name = trimr 6 result_name ^ "exec_def"
  val exec_def = fetch thyn exec_def_name
  val () = Feedback.HOL_MESG $ String.concat ["Evaluating ", exec_def_name]
  val exec_eval = Timeout.apply limit (CONV_RULE $ RAND_CONV cv_eval_raw) exec_def

  Timeout.apply limit
  signature Timeout = Timeout
  signature TIME = TIME

val () = Globals.max_print_depth := 15;
val limit = Time.fromSeconds 120;
val thyn = "vfmStateTestDefs10"
val result_defs = get_result_defs thyn;
val (result_def_name, result_def) = el 3 result_defs

val result_thms = List.map (I ## CONV_RULE (RAND_CONV cv_eval)) result_defs;

val () = List.app (fn (result_name, thm) =>
           ignore $ save_thm(
             Substring.string (Substring.trimr 4 (Substring.full result_name)),
             thm)) result_thms

val result_defs = "vfmStateTestDefs200"
  |> definitions |> List.filter (String.isSuffix "result_def" o #1);

(* TODO: add timing and timeouts *)
val result_thms = List.map (I ## CONV_RULE (RAND_CONV cv_eval)) result_defs;

val () = List.app (fn (result_name, thm) =>
           ignore $ save_thm(
             Substring.string (Substring.trimr 4 (Substring.full result_name)),
             thm)) result_thms

val () = export_theory_no_docs ();
