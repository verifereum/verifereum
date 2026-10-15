structure vfmTestResultLib :> vfmTestResultLib = struct

  open HolKernel boolLib bossLib vfmTestAuxLib cv_transLib
       vfmTestAuxLib vfmTestRunTheory stringSyntax wordsSyntax

  val get_result_defs =
     List.filter (String.isSuffix "result_def" o #1) o
     definitions

  (* The genesis state root check dominates evaluation, and tests in a file
     often share their pre-state, or storage maps and code within it. Each
     distinct value is proved once by cv_eval, cached here for the rest of
     the file, and the per-test evaluation starts from the proved root. *)

  val storage_root_tm = prim_mk_const{Thy="vfmRoot",Name="storage_root"}
  val state_root_tm = prim_mk_const{Thy="vfmRoot",Name="state_root"}
  val keccak_tm = prim_mk_const{Thy="keccak",Name="Keccak_256_w64"}
  val update_account_tm = prim_mk_const{Thy="vfmState",Name="update_account"}
  val state_root_memo_tm =
    prim_mk_const{Thy="vfmTestRun",Name="state_root_memo"}

  fun empty_cache () = ref $ Redblackmap.mkDict Term.compare
  val storage_root_cache : (term, thm) Redblackmap.dict ref = empty_cache ()
  val code_hash_cache : (term, thm) Redblackmap.dict ref = empty_cache ()
  val state_root_cache : (term, thm) Redblackmap.dict ref = empty_cache ()

  fun cached cache prove key =
    case Redblackmap.peek(!cache, key) of
      SOME th => th
    | NONE => let
        val th = prove key
        val () = cache := Redblackmap.insert(!cache, key, th)
      in th end

  fun account_list tm =
    case strip_comb tm of
      (c, [_, account, rest]) =>
        if same_const c update_account_tm
        then account :: account_list rest
        else []
    | _ => []

  fun account_field name account =
    Lib.assoc name $ #2 $ TypeBase.dest_record account

  (* Theorems `f k = v` for the distinct k among keys, each proved once. *)
  fun lemmas_for cache f keys = let
    fun prove k = cv_eval $ mk_comb(f, k)
    val distinct = Redblackset.addList(Redblackset.empty Term.compare, keys)
  in
    List.map (cached cache prove) $ Redblackset.listItems distinct
  end

  (* The table [(k, v); ...] of lemmas ⊢ f k = v, and
     ⊢ EVERY (λ(k,v). f k = v) table. *)
  fun lemma_table f lemmas = let
    val (key_ty, value_ty) = dom_rng $ type_of f
    val k = mk_var("k", key_ty)
    val v = mk_var("v", value_ty)
    val pred = pairSyntax.mk_pabs(pairSyntax.mk_pair(k, v),
                                  mk_eq(mk_comb(f, k), v))
    fun entry th = pairSyntax.mk_pair(rand $ lhs $ concl th, rhs $ concl th)
    val table = listSyntax.mk_list(List.map entry lemmas,
                                   pairSyntax.mk_prod(key_ty, value_ty))
    val valid = EQT_ELIM $ SIMP_CONV bool_ss
      (listTheory.EVERY_DEF :: pairTheory.UNCURRY_DEF :: lemmas)
      (listSyntax.mk_every(pred, table))
  in
    (table, valid)
  end

  (* ⊢ state_root pre = root, where pre_def is ⊢ pre = accounts. *)
  fun prove_state_root pre_def = let
    val pre = lhs $ concl pre_def
    val accounts = account_list $ rhs $ concl pre_def
    val storage_lemmas = lemmas_for storage_root_cache storage_root_tm $
      List.map (account_field "storage") accounts
    val code_lemmas = lemmas_for code_hash_cache keccak_tm $
      List.map (account_field "code") accounts
    val (st, st_valid) = lemma_table storage_root_tm storage_lemmas
    val (ct, ct_valid) = lemma_table keccak_tm code_lemmas
    val memo_eq = SPEC pre $ MATCH_MP state_root_memo_thm $
      CONJ st_valid ct_valid
  in
    TRANS (SYM memo_eq) $ cv_eval $ list_mk_comb(state_root_memo_tm, [st, ct, pre])
  end

  (* ⊢ state_root pre = root, proved once per distinct pre-state. *)
  fun state_root_thm pre_def = let
    val accounts = rhs $ concl pre_def
    fun prove _ = TRANS (AP_TERM state_root_tm $ SYM pre_def)
                        (prove_state_root pre_def)
  in
    TRANS (AP_TERM state_root_tm pre_def)
          (cached state_root_cache prove accounts)
  end

  fun eval_rhs thyn result_def = let
    val pre = hd $ #2 $ strip_comb $ rhs $ concl result_def
    val pre_def = fetch thyn (#1 (dest_const pre) ^ "_def")
    val root = state_root_thm pre_def
  in
    CONV_RULE (RAND_CONV (
      REWR_CONV run_test_def THENC
      PURE_ONCE_REWRITE_CONV [root] THENC
      cv_eval)) result_def
  end

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
    val result_eval = Timeout.apply time_limit (eval_rhs thyn) result_def
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
      String.concatWith "\n" [test_name, result_str, time_str, "checked"])
    val () = TextIO.output(out, "\n")
    val () = TextIO.closeOut out
  in
    save_thm(result_name, result_eval)
  end

end
