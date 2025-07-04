structure vfmTestResultLib :> vfmTestResultLib = struct

  open HolKernel boolLib bossLib vfmTestAuxLib cv_transLib
       vfmTestAuxLib vfmTestRunTheory stringSyntax wordsSyntax

  val get_result_defs =
     List.filter (String.isSuffix "result_def" o #1) o
     definitions

  val eval_rhs = CONV_RULE $ RAND_CONV cv_eval;

  fun test_result_to_string tm =
    if is_comb tm then let
      val (ct, at) = dest_comb tm
      val c = #1 $ dest_const ct
      val a = if is_string at
               then fromHOLstring at
               else String.concat ["0x", Arbnum.toHexString $
                                         numSyntax.dest_numeral $
                                         #1 $ dest_n2w at]
      in String.concat [c, " ", a] end
    else #1 $ dest_const tm

  fun mk_result_string tm =
    if is_eq tm
    then test_result_to_string $ rhs tm
    else "Timeout"

  fun save_result_thm thyn (result_def_name, result_def) = let
    val result_name = trimr (String.size "_def") result_def_name
    val () = Feedback.HOL_MESG $
      String.concat ["Evaluating ", result_name,
                     " for up to ", Time.fmt 0 time_limit, "s" ]
    val start_time = Time.now()
    val result_eval = Timeout.apply time_limit eval_rhs result_def
                      handle Timeout.TIMEOUT _ => TRUTH
    val end_time = Time.now()
    val result_str = mk_result_string $ concl result_eval
    val time_spent = end_time - start_time
    val time_str = Time.fmt 2 time_spent
    val () = Feedback.HOL_MESG $ String.concat $ [
               result_name, " = ", result_str, " (", time_str, "s)"
             ]
    val test_prefix = trimr (String.size "_result") result_name
    val len = String.size test_prefix
    val strip = String.size "test_"
    val result_suffix = String.substring(test_prefix, strip, len - strip)
    val csv_name = "result" ^ result_suffix ^ ".nsv"
    val test_name = fromHOLstring $ rhs $ concl $
                    fetch thyn $ test_prefix ^ "_name_def"
    val out = TextIO.openOut csv_name
    val () = TextIO.output(out,
      String.concatWith "\n" [test_name, result_str, time_str])
    val () = TextIO.output(out, "\n")
    val () = TextIO.closeOut out
  in
    save_thm(result_name, result_eval)
  end

end
