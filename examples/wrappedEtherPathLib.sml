(* ------------------------------------------------------------------------
   wrappedEtherPathLib: a path of WETH's block summaries (wrappedEtherTheory),
   composed, its memory reads simplified, and lifted to run_transaction
   through SPEC_to_run_transaction or SPEC_to_run_transaction_failure. Used
   by the theories proving WETH's functions over run_transaction.
   ------------------------------------------------------------------------ *)

structure wrappedEtherPathLib =
struct

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory combinTheory pairTheory
     pred_setTheory byteTheory wordsTheory
     vfmTypesTheory vfmConstantsTheory vfmStateTheory vfmContextTheory
     vfmExecutionTheory vfmBufferTheory set_sepTheory progTheory
     vfmProgTheory contractABITheory wrappedEtherTheory;
open wordsLib cv_transLib evmDecompLib;

(* ---------------------------------------------------------------- *)
(* Composing a path of block summaries *)

fun weth_block n v =
  DB.fetch "wrappedEther" ("weth_block_" ^ Int.toString n ^ v)

val memory_cost_64_32 =
  Q.SPECL [`64`,`32`] (Q.GENL [`off`,`sz`] memory_cost_offset_to_0)
  |> SIMP_RULE arith_ss []

fun ground_div_conv tm =
  let val (f, _) = strip_comb tm in
    if is_const f andalso
       Lib.mem (fst (dest_const f)) ["with_zero", "word_div"] andalso
       null (free_vars tm)
    then
      let val th = EVAL tm in
        if rhs (concl th) ~~ tm then raise UNCHANGED else th
      end
    else raise UNCHANGED
  end
val ground_div_ss = simpLib.named_merge_ss "ground_div" [simpLib.conv_ss
  {name = "ground_div", trace = 3, key = SOME ([], mk_var ("x", alpha)),
   conv = K (K ground_div_conv)}]

(* f x with closed divisions evaluated by srw_ss *)
fun with_ground_div f x =
  let
    val () = augment_srw_ss [ground_div_ss]
    val r = f x handle e => (diminish_srw_ss ["ground_div"]; raise e)
  in
    diminish_srw_ss ["ground_div"]; r
  end

val path_config : evmDecompLib.config =
  {code_eq = contract_code_eq, parsed_eq = parsed_contract_code_eq,
   hints = [],
   simps = [with_zero_def, mask_and_w2w, memory_cost_64_32,
            accesses_add_slot_accounts, buffer_take_write_same,
            buffer_take_write_after, buffer_take_write_before,
            buffer_take_expanded_memory, buffer_length_expanded_memory,
            word_to_bytes_bytes32_NIL,
            buffer_take_split |> Q.INST [`n1` |-> `32`, `n2` |-> `32`]
                              |> SIMP_RULE arith_ss [],
            MAX_LE, expanded_memory_leq, memory_cost_none_zero,
            memory_cost_buffer_write, memory_cost_add],
   strip_metadata = true}

fun var_named th n =
  valOf (List.find (fn v => fst (dest_var v) = n) (thm_frees th))

(* the summaries weth_block_<n><v> of a path from pc 0, composed with the
   memory abbreviations kept, spelt out at the end *)
fun compose_path0 path =
  let
    val ths = map (fn (n, v) => weth_block n v) path
    val th0 = hd ths
    val th0 = INST [var_named th0 "m" |-> “empty_buffer”,
                    var_named th0 "g" |-> “0n”] th0
  in
    inline_memory (List.foldl (fn (th, acc) =>
      compose_blocks path_config [acc, th]) th0 (tl ths))
  end

val compose_path = with_ground_div compose_path0

(* ---------------------------------------------------------------- *)
(* Reading the composed path's memory

   Spelt out, the path's memory is a deep term with much sharing: each
   buffer_write's offset reads the free memory pointer back from the
   memory below it. Simplifying it as a term takes minutes. Instead each
   distinct memory term t gets, once, its contents buffer_to_list t = L as
   a short list (chunks of 32 bytes, closed parts evaluated) and its
   length; the reads of the path (buffer_take, buffer_length, memory_cost,
   Keccak256_gas) are rewritten with those, and memory terms are never
   traversed. A memory is worked on as a variable standing for the memory
   below it, with that one's contents as hypotheses, then instantiated. *)

val buffer_ty = “:buffer”

fun is_app n k tm =
  let val (f, xs) = strip_comb tm in
    is_const f andalso fst (dest_const f) = n andalso length xs = k
  end

(* evaluates closed byte lists and numbers inside a small term *)
fun ground_bytes_conv tm =
  if null (free_vars tm) andalso
     not (listSyntax.is_list tm andalso
          List.all wordsSyntax.is_word_literal (fst (listSyntax.dest_list tm)))
  then
    let val th = EVAL tm in
      if rhs (concl th) ~~ tm then raise UNCHANGED else th
    end
  else raise UNCHANGED

val ground_bytes_ss = simpLib.named_merge_ss "ground_bytes" [simpLib.conv_ss
  {name = "ground_bytes", trace = 3, key = SOME ([], mk_var ("x", “:word8 list”)),
   conv = K (K ground_bytes_conv)}]

(* closed word_of_bytes by cv_eval, as evmDecompLib does: EVAL unfolds
   it into set_byte chains *)
val word_of_bytes_ss = simpLib.conv_ss
  {name = "word_of_bytes_ss", trace = 3,
   key = SOME ([], “word_of_bytes F (0w : 'a word) (l : word8 list)”),
   conv = K (K (fn tm =>
     if null (free_vars tm) then
       (REWR_CONV (SRULE [FUN_EQ_THM] (GSYM word_of_bytes_le_def))
        THENC cv_transLib.cv_eval) tm
     else raise mk_HOL_ERR "wrappedEtherPathLib" "word_of_bytes_ss"
                  "not ground"))}

(* the same as a conversion, before srw_ss sees the list *)
val word_of_bytes_conv = DEPTH_CONV (fn tm =>
  if is_app "word_of_bytes" 3 tm andalso null (free_vars tm) then
    (REWR_CONV (SRULE [FUN_EQ_THM] (GSYM word_of_bytes_le_def))
     THENC cv_transLib.cv_eval) tm
  else NO_CONV tm)

val list_conv =
  QCONV word_of_bytes_conv THENC SIMP_CONV (srw_ss() ++ word_of_bytes_ss ++ ground_bytes_ss ++ ARITH_ss)
    [TAKE_APPEND, DROP_APPEND, LENGTH_word_to_bytes, PAD_RIGHT,
     TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG, memory_expand_by_def,
     word_to_bytes_bytes32_NIL, MAX_DEF, word_size_def]

val memory_cache : (term, thm * thm) Redblackmap.dict ref =
  ref (Redblackmap.mkDict Term.compare)

(* the path's terms share subterms (the same key or gas term in many
   places): reads are cached by term, NONE for unchanged *)
val reads_cache : (term, thm option) Redblackmap.dict ref =
  ref (Redblackmap.mkDict Term.compare)

(* buffer_length v = n from buffer_to_list v = L *)
fun length_of thL =
  let val v = rand (lhs (concl thL)) in
    TRANS (SYM (PART_MATCH lhs LENGTH_buffer_to_list
                  (mk_comb (“LENGTH : word8 list -> num”, lhs (concl thL)))))
      (AP_TERM “LENGTH : word8 list -> num” thL)
    |> CONV_RULE (RAND_CONV list_conv)
  end

(* (buffer_to_list t = L, buffer_length t = n) *)
fun memory_of t =
  case Redblackmap.peek (!memory_cache, t) of SOME r => r | NONE =>
  let
    val r =
      if is_const t andalso fst (dest_const t) = "empty_buffer" then
        let val thL = EVAL (mk_comb (“buffer_to_list”, t)) in
          (thL, length_of thL)
        end
      else if is_app "expanded_memory" 3 t orelse is_app "buffer_write" 3 t
      then
        let
          (* the memory below, and the other arguments with their reads
             rewritten *)
          val (f, args) = strip_comb t
          val ths = map (fn a => if type_of a = buffer_ty then REFL a
                                 else QCONV (TRY_CONV reads_conv THENC
                                             word_of_bytes_conv) a)
                        args
          val m = valOf (List.find (fn a => type_of a = buffer_ty) args)
          val eq = AP_TERM “buffer_to_list”
                     (List.foldl (fn (th, acc) => MK_COMB (acc, th)) (REFL f) ths)
          val args' = map (rhs o concl) ths
          val (thL', _) = under m (fn v =>
             list_mk_comb (f, map (fn a => if a ~~ m then v else a) args'))
             [expanded_memory_def, buffer_to_list_extend, buffer_to_list_write]
          val thL = TRANS eq thL'
        in (thL, length_of thL) end
      else raise mk_HOL_ERR "wrappedEtherPathLib" "memory_of"
                   "not a closed memory"
  in memory_cache := Redblackmap.insert (!memory_cache, t, r); r end
and cost_conv tm =
  if null (free_vars tm) then EVAL tm
  else SIMP_CONV (srw_ss() ++ ARITH_ss)
         [memory_expansion_cost_def, word_size_def] tm
(* the memory mk v built on v standing for m *)
and under m mk ths =
  let
    val (thLm, thNm) = memory_of m
    val v = genvar buffer_ty
    val hL = ASSUME (mk_eq (mk_comb (“buffer_to_list”, v), rhs (concl thLm)))
    val hN = ASSUME (mk_eq (mk_comb (“buffer_length”, v), rhs (concl thNm)))
    val tm = mk_comb (“buffer_to_list”, mk v)
    val th1 = SIMP_CONV (srw_ss())
                (ths @ [memory_expand_by_def, word_to_bytes_bytes32_NIL,
                        hL, hN]) tm
    val th = TRANS th1 (QCONV list_conv (rhs (concl th1)))
    val th = PROVE_HYP thNm (PROVE_HYP thLm (INST [v |-> m] th))
  in (th, length_of th) end
(* rewrites the reads of closed memories in tm, not looking into memories *)
and reads_conv tm =
  if not (is_comb tm) orelse type_of tm = buffer_ty then raise UNCHANGED
  else
    case Redblackmap.peek (!reads_cache, tm) of
      SOME (SOME th) => th
    | SOME NONE => raise UNCHANGED
    | NONE =>
        let
          val r = SOME (reads_conv0 tm) handle UNCHANGED => NONE
        in
          reads_cache := Redblackmap.insert (!reads_cache, tm, r);
          case r of SOME th => th | NONE => raise UNCHANGED
        end
and reads_conv0 tm =
  if type_of tm = buffer_ty then raise UNCHANGED
  else if is_app "buffer_take" 3 tm then
    ((args_conv THENC REWR_CONV buffer_take_to_list THENC
      RAND_CONV (RAND_CONV (fn t => #1 (memory_of (rand t)))) THENC list_conv) tm
     handle HOL_ERR _ => SUB_CONV reads_conv tm)
  else if is_app "buffer_length" 1 tm then
    (#2 (memory_of (rand tm)) handle HOL_ERR _ => raise UNCHANGED)
  else if is_app "memory_cost" 3 tm then
    ((args_conv THENC REWR_CONV vfmProgTheory.memory_cost_def THENC
      RATOR_CONV (RAND_CONV (fn l => #2 (memory_of (rand l)))) THENC
      cost_conv) tm
     handle HOL_ERR _ => SUB_CONV reads_conv tm)
  else if is_app "Keccak256_gas" 3 tm then
    ((args_conv THENC REWR_CONV Keccak256_gas_def THENC
      ONCE_DEPTH_CONV (fn t => if is_app "memory_cost" 3 t then reads_conv t
                               else NO_CONV t) THENC
      cost_conv) tm
     handle HOL_ERR _ => SUB_CONV reads_conv tm)
  else SUB_CONV reads_conv tm
(* the reads in the arguments that are not memories *)
and args_conv tm =
  let
    val (f, args) = strip_comb tm
    val ths = map (fn a => if type_of a = buffer_ty then REFL a
                           else QCONV (TRY_CONV reads_conv THENC
                                       word_of_bytes_conv) a) args
  in
    List.foldl (fn (th, acc) => MK_COMB (acc, th)) (REFL f) ths
  end
(* the composed path with its memory reads rewritten *)
val path_reads =
  with_ground_div (CONV_RULE (helperLib.PRE_POST_CONV reads_conv))


(* the balance slots' keys hashed as balance_slot_key does *)
val balance_slot_key_bytes =
  balance_slot_key_def
  |> REWRITE_RULE [word_of_bytes_be_def, balance_slot_word_def,
                   word_to_bytes_le_def]
  |> CONV_RULE (QUANT_CONV (RAND_CONV (ONCE_DEPTH_CONV (fn t =>
       if is_app "REVERSE" 1 t andalso null (free_vars t) then EVAL t
       else NO_CONV t))))
  |> GSYM

fun path_keys th =
  let val th' = PURE_REWRITE_RULE [balance_slot_key_bytes] th in
    if null (hyp th') then th'
    else raise mk_HOL_ERR "wrappedEtherPathLib" "path_keys"
           "hypotheses"
  end

(* a call's start: no pending exception or jump, no outer contexts, an
   empty stack, and not a create, so no code deposit (codeCost, which only
   a path ending in RETURN has) *)
fun spec_start th =
  let
    val e = var_named th "e" and j = var_named th "j"
    val cs = var_named th "cs" and rest = var_named th "rest"
    val codeCost =
      case List.find (fn v => fst (dest_var v) = "codeCost") (thm_frees th) of
        SOME v => [v |-> “0n”]
      | NONE => []
  in
    INST ([e |-> sumSyntax.mk_inl (“()”, snd (sumSyntax.dest_sum (type_of e))),
           j |-> optionSyntax.mk_none (optionSyntax.dest_option (type_of j)),
           cs |-> listSyntax.mk_nil (listSyntax.dest_list_type (type_of cs)),
           rest |-> listSyntax.mk_nil (listSyntax.dest_list_type (type_of rest))]
          @ codeCost) th
  end

(* ---------------------------------------------------------------- *)
(* Lifting the path to run_transaction *)

fun evc tm = tm |> (REWRITE_CONV [parsed_contract_code_eq] THENC EVAL)

(* the path's instructions are entries of the parsed code *)
fun spec_code spec_start =
  let
    val th = MATCH_MP SPEC_SUBSET_CODE spec_start
             |> SPEC “fmap_entries parsed_contract_code”
    val tac = rewrite_tac [SUBSET_DEF] \\ Cases
      \\ rewrite_tac [IN_INSERT, NOT_IN_EMPTY, PAIR_EQ]
      \\ strip_tac \\ rpt BasicProvers.VAR_EQ_TAC
      \\ simp [fmap_entries_def] \\ CONV_TAC evc
    val sub = prove (fst (dest_imp (concl th)), tac)
  in
    MP th sub
  end

(* framed with the transaction parameters, which run_transaction's lifting
   names, the code moved into the pre- and postcondition *)
fun spec_pool spec_code =
  SPEC “evm_TxParams txParams * SEP_T”
    (MATCH_MP SPEC_FRAME spec_code)
  |> ONCE_REWRITE_RULE [GSYM SPEC_CODE]
  |> REWRITE_RULE [FST_SND_SND_EVM_MODEL]

fun dest_star tm =
  case strip_comb tm of
    (f, [a, b]) =>
      if is_const f andalso fst (dest_const f) = "STAR" then (f, a, b)
      else raise mk_HOL_ERR "wrappedEtherPathLib" "dest_star" ""
  | _ => raise mk_HOL_ERR "wrappedEtherPathLib" "dest_star" ""

fun strip_star tm =
  let val (_, a, b) = dest_star tm in strip_star a @ strip_star b end
  handle HOL_ERR _ => [tm]

(* the postcondition in the order a lifting theorem names it *)
fun spec_ordered names spec_pool =
  let
    val post = rand (concl spec_pool)
    val (star, _, _) = dest_star post
    fun mk_star (a, b) = list_mk_comb (star, [a, b])
    fun head_name tm =
      let val f = fst (strip_comb tm) in
        if is_const f then fst (dest_const f) else ""
      end
    val factors = strip_star post
    val picked = map (fn n => valOf (List.find (fn f => head_name f = n)
                                       factors)) names
    val others = List.filter (fn f => not (Lib.mem (head_name f) names))
                   factors
    val rest = List.foldl (fn (f, acc) => mk_star (acc, f))
                 (hd others) (tl others)
    val post' = List.foldl (fn (f, acc) => mk_star (acc, f))
                  (hd picked) (tl picked @ [rest])
    val eq = EQT_ELIM (SIMP_CONV bool_ss [AC STAR_ASSOC STAR_COMM]
                         (mk_eq (post, post')))
  in
    CONV_RULE (RAND_CONV (REWR_CONV eq)) spec_pool
  end

fun spec_lift lift_thm spec_ordered =
  let
    val th = MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] lift_thm)
               spec_ordered
    val (ants, _) = strip_imp (concl th)
    val (q, form) = dest_eq (last ants)
    val (tmS, tyS) = match_term form q
    val th = INST tmS (INST_TYPE tyS th) |> REWRITE_RULE [AND_IMP_INTRO]
  in
    (* MATCH_MP primed the lifting theorem's states; name them s and s' *)
    INST [var_named th "s''" |-> mk_var ("s", “:execution_state”),
          var_named th "s'''" |-> mk_var ("s'", “:execution_state”)] th
  end

(* bounds the path's access and SSTORE costs in the goal by their worst case *)
fun gas_bounds_tac (asl, w) =
  let
    fun is_cost t =
      is_app "access_slot_cost" 2 t orelse is_app "sstore_base_gas" 3 t
    val ts = HOLset.listItems (HOLset.addList (empty_tmset, find_terms is_cost w))
    fun bound t =
      if is_app "access_slot_cost" 2 t then
        PART_MATCH (rand o rator) access_slot_cost_le t
      else PART_MATCH (rand o rator) sstore_base_gas_le t
  in
    MAP_EVERY (assume_tac o bound) ts (asl, w)
  end

end
