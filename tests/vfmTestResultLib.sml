structure vfmTestResultLib :> vfmTestResultLib = struct

  open HolKernel boolLib bossLib vfmTestAuxLib cv_transLib

  val get_result_defs =
    List.filter (String.isSuffix "result_def" o #1) o
    definitions

  val eval_rhs = CONV_RULE $ RAND_CONV cv_eval;

  fun save_result_thm limit (result_def_name, result_def) = let
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
    save_thm(result_name, result_eval)
  end

end
