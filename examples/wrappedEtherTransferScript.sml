(* WETH's transfer(dst,wad), from the block summaries of wrappedEtherTheory
   composed along its path and lifted to run_transaction. *)
Theory wrappedEtherTransfer
Ancestors
  arithmetic list rich_list combin pair pred_set byte cv_std words
  vfmTypes vfmConstants vfmState vfmContext vfmExecution vfmExecutionProp
  vfmBuffer
  set_sep prog vfmProg contractABI wrappedEther wrappedEtherName
Libs
  dep_rewrite wordsLib cv_transLib evmDecompLib

(* ---------------------------------------------------------------- *)
(* The transfer as a change of WETH_state *)

Definition WETH_transfer_def:
  WETH_transfer src dst n ws =
  let b = (src =+ ws.balances src - n) ws.balances in
  ws with <| balances := (dst =+ b dst + n) b
           ; touched updated_by (INSERT) dst |>
End

Theorem SUM_IMAGE_INSERT_ZERO[local]:
  FINITE (ys:'a set) ∧ (y ∉ ys ⇒ g y = 0n) ⇒
  SIGMA g (y INSERT ys) = SIGMA g ys
Proof
  rpt strip_tac
  \\ Cases_on `y ∈ ys` >- simp[iffLR ABSORPTION]
  \\ simp[SUM_IMAGE_INSERT]
QED

Theorem wf_WETH_transfer:
  wf_WETH_state ws ∧ n ≤ ws.balances src ⇒
  wf_WETH_state (WETH_transfer src dst n ws)
Proof
  strip_tac
  \\ `∀a. a ∉ ws.touched ⇒ ws.balances a = 0`
     by (gvs[wf_WETH_state_def, SUBSET_DEF] \\ metis_tac[NOT_ZERO_LT_ZERO])
  \\ Cases_on `n = 0 ∨ src = dst`
  >- (
    `WETH_transfer src dst n ws = ws with touched := dst INSERT ws.touched`
      by (rw[WETH_transfer_def, WETH_state_component_equality,
             FUN_EQ_THM, APPLY_UPDATE_THM] \\ rw[] \\ gvs[])
    \\ gvs[wf_WETH_state_def, SUBSET_DEF, total_balances_def,
           SUM_IMAGE_INSERT_ZERO])
  \\ gvs[]
  \\ `ws.balances src < 2 ** 256 ∧ ws.balances dst < 2 ** 256`
     by gvs[wf_WETH_state_def]
  \\ `src ∈ ws.touched` by (CCONTR_TAC \\ res_tac \\ gvs[])
  \\ qabbrev_tac `T0 = ws.touched DELETE src DELETE dst`
  \\ `dst INSERT ws.touched = dst INSERT src INSERT T0`
     by (rw[Abbr`T0`, EXTENSION] \\ metis_tac[])
  \\ `dst ∉ src INSERT T0 ∧ src ∉ T0` by simp[Abbr`T0`]
  \\ `SIGMA ws.balances ws.touched =
      ws.balances dst + ws.balances src + SIGMA ws.balances T0`
     by (`SIGMA ws.balances ws.touched =
          SIGMA ws.balances (dst INSERT ws.touched)`
           by simp[SUM_IMAGE_INSERT_ZERO]
         \\ pop_assum SUBST1_TAC \\ simp[SUM_IMAGE_INSERT])
  \\ qmatch_goalsub_abbrev_tac `wf_WETH_state ws'`
  \\ `ws'.balances dst = ws.balances dst + n ∧
      ws'.balances src = ws.balances src - n ∧
      ∀a. a ≠ src ∧ a ≠ dst ⇒ ws'.balances a = ws.balances a`
     by simp[Abbr`ws'`, WETH_transfer_def, APPLY_UPDATE_THM]
  \\ `ws'.touched = dst INSERT ws.touched ∧ ws'.allowances = ws.allowances ∧
      ws'.locked = ws.locked`
     by simp[Abbr`ws'`, WETH_transfer_def]
  \\ `SIGMA ws'.balances T0 = SIGMA ws.balances T0`
     by (irule SUM_IMAGE_CONG \\ simp[Abbr`T0`])
  \\ gvs[wf_WETH_state_def, total_balances_def, SUBSET_DEF, SUM_IMAGE_INSERT]
  \\ rw[]
  \\ Cases_on `a = src` \\ Cases_on `a = dst`
  \\ Cases_on `x = src` \\ Cases_on `x = dst`
  \\ gvs[Abbr`T0`]
  \\ metis_tac[]
QED

(* ---------------------------------------------------------------- *)
(* Calldata for transfer(dst, wad) *)

Theorem transfer_selector_eq:
  function_selector "transfer" [Address; Uint 256] =
  [0xA9w; 0x05w; 0x9Cw; 0xBBw]
Proof
  CONV_TAC (LAND_CONV cv_eval) \\ rw[]
QED

Theorem transfer_args_enc:
  enc (Tuple [Address; Uint 256]) (ListV [NumV (w2n dst); NumV wad]) =
  word_to_bytes (w2w (dst:address) : bytes32) T ++
  word_to_bytes (n2w wad : bytes32) T
Proof
  simp[head_lengths_def, w2w_def, REV_DEF]
QED

Theorem transfer_selector_calldata:
  0xFFFFFFFFw &&
  word_of_bytes F 0w
    (REVERSE (take_pad_0 32 ([0xA9w; 0x05w; 0x9Cw; 0xBBw] ++ rest))) //
  (0x100000000000000000000000000000000000000000000000000000000w : bytes32)
  = 0xA9059CBBw
Proof
  qabbrev_tac `sel = [0xA9w; 0x05w; 0x9Cw; 0xBBw] : word8 list`
  \\ `∃r. take_pad_0 32 (sel ++ rest) = sel ++ r ∧ LENGTH r = 28`
  by rw[take_pad_0_def, TAKE_APPEND, PAD_RIGHT, Abbr`sel`, LENGTH_TAKE_EQ]
  \\ simp[GSYM word_of_bytes_le_def]
  \\ DEP_REWRITE_TAC[word_of_bytes_le_eq_num_of_bytes]
  \\ simp[REVERSE_APPEND, num_of_bytes_APPEND, word_div_def]
  \\ qspec_then `REVERSE r` assume_tac num_of_bytes_lt
  \\ `num_of_bytes (REVERSE sel) = 0xA9059CBB`
  by simp[Abbr`sel`, num_of_bytes_def, dimword_8]
  \\ gvs[]
  \\ `num_of_bytes (REVERSE r) + 256 ** 28 * 0xA9059CBB < dimword (:256)`
  by simp[]
  \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ qmatch_goalsub_abbrev_tac `(a + b) DIV c`
  \\ `a < c` by simp[Abbr`a`, Abbr`c`]
  \\ `(a + b) DIV c = 2835717307`
  by (`a + b = 2835717307 * c + a` by simp[Abbr`b`, Abbr`c`]
      \\ pop_assum SUBST1_TAC
      \\ simp[ADD_DIV_ADD_DIV, LESS_DIV_EQ_ZERO, Abbr`c`])
  \\ simp[]
QED

Theorem REVERSE_word_to_bytes_bytes32:
  REVERSE (word_to_bytes (w:bytes32) T) = word_to_bytes w F ∧
  REVERSE (word_to_bytes (w:bytes32) F) = word_to_bytes w T
Proof
  rewrite_tac[GSYM word_to_bytes_be_def, GSYM word_to_bytes_le_def,
              word_to_bytes_be_eq_bytes_of_num,
              word_to_bytes_le_eq_bytes_of_num, REVERSE_REVERSE]
QED

(* an argument word read from the calldata *)
Theorem calldata_word:
  word_of_bytes F 0w
    (REVERSE (take_pad_0 32 (word_to_bytes (w:bytes32) T ++ r))) = w ∧
  word_of_bytes F 0w
    (REVERSE (take_pad_0 32 (word_to_bytes (w:bytes32) T ++ r1 ++ r2))) = w
Proof
  rewrite_tac[GSYM APPEND_ASSOC]
  \\ simp[take_pad_0_def, TAKE_APPEND, PAD_RIGHT, TAKE_LENGTH_ID_rwt,
       REVERSE_word_to_bytes_bytes32]
QED

(* ---------------------------------------------------------------- *)
(* The transfer path, composed from the block summaries *)

fun weth_block n v =
  DB.fetch "wrappedEther" ("weth_block_" ^ Int.toString n ^ v)

(* the selector chain to 880, the callvalue check, the argument decoding
   at 891, transfer at 3022 calling transferFrom at 1676 with the caller
   as source: the balance check, src = caller skipping the allowance
   (1756, 1972), the balance updates and the Transfer log at 2255, back
   through 3035 to the return at 944 *)
val transfer_path =
  [(0, "_skip"), (13, "_skip"), (65, "_skip"), (76, "_skip"), (87, "_skip"),
   (98, "_skip"), (109, "_skip"), (120, "_skip"), (131, "_skip"),
   (142, "_take"), (880, "_take"), (891, "_Jump"), (3022, "_Jump"),
   (1676, "_take"), (1756, "_take"), (1972, "_take"), (2255, "_Jump"),
   (3035, "_Jump"), (944, "_outermost")]

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
val () = augment_srw_ss [simpLib.named_merge_ss "ground_div" [simpLib.conv_ss
  {name = "ground_div", trace = 3, key = SOME ([], mk_var ("x", alpha)),
   conv = K (K ground_div_conv)}]]

val transfer_config : evmDecompLib.config =
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

(* composed with the memory abbreviations kept, spelt out at the end *)
val transfer_path_abbrev =
  let
    val ths = map (fn (n, v) => weth_block n v) transfer_path
    val th0 = hd ths
    val th0 = INST [var_named th0 "m" |-> “empty_buffer”,
                    var_named th0 "g" |-> “0n”] th0
  in
    List.foldl (fn ((th, (n, _)), acc) =>
      compose_blocks transfer_config [acc, th])
      th0 (zip (tl ths) (tl transfer_path))
  end

val transfer_path_composed =
  inline_memory transfer_path_abbrev

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
     else raise mk_HOL_ERR "wrappedEtherTransferScript" "word_of_bytes_ss"
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
      else raise mk_HOL_ERR "wrappedEtherTransferScript" "memory_of"
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
val transfer_path_reads =
  CONV_RULE (helperLib.PRE_POST_CONV reads_conv) transfer_path_composed

val () = diminish_srw_ss ["ground_div"]

(* the balance slots' keys hashed as balance_slot_key does *)
Theorem balance_slot_key_bytes[local] =
  balance_slot_key_def
  |> REWRITE_RULE [word_of_bytes_be_def, balance_slot_word_def,
                   word_to_bytes_le_def]
  |> CONV_RULE (QUANT_CONV (RAND_CONV (ONCE_DEPTH_CONV (fn t =>
       if is_app "REVERSE" 1 t andalso null (free_vars t) then EVAL t
       else NO_CONV t))))
  |> GSYM

val transfer_path_keys =
  PURE_REWRITE_RULE [balance_slot_key_bytes] transfer_path_reads

val () = if null (hyp transfer_path_keys) then ()
         else raise mk_HOL_ERR "wrappedEtherTransferScript" "transfer_path_keys"
                "hypotheses"

(* a call's start: no pending exception or jump, no outer contexts, an
   empty stack, and not a create, so no code deposit *)
val transfer_spec_start =
  let
    val th = transfer_path_keys
    val e = var_named th "e" and j = var_named th "j"
    val cs = var_named th "cs" and rest = var_named th "rest"
    val codeCost = var_named th "codeCost"
  in
    INST [e |-> sumSyntax.mk_inl (“()”, snd (sumSyntax.dest_sum (type_of e))),
          j |-> optionSyntax.mk_none (optionSyntax.dest_option (type_of j)),
          cs |-> listSyntax.mk_nil (listSyntax.dest_list_type (type_of cs)),
          rest |-> listSyntax.mk_nil (listSyntax.dest_list_type (type_of rest)),
          codeCost |-> “0n”] th
  end

Theorem FST_SND_SND_EVM_MODEL[local]:
  FST (SND (SND EVM_MODEL)) = EVM_INSTR
Proof
  rw[EVM_MODEL_def]
QED

(* ---------------------------------------------------------------- *)
(* Lifting the path to run_transaction *)

fun evc tm = tm |> (REWRITE_CONV [parsed_contract_code_eq] THENC EVAL)

(* the path's instructions are entries of the parsed code *)
val transfer_spec_code =
  let
    val th = MATCH_MP SPEC_SUBSET_CODE transfer_spec_start
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
val transfer_spec_pool =
  SPEC “evm_TxParams txParams * SEP_T”
    (MATCH_MP SPEC_FRAME transfer_spec_code)
  |> ONCE_REWRITE_RULE [GSYM SPEC_CODE]
  |> REWRITE_RULE [FST_SND_SND_EVM_MODEL]

fun dest_star tm =
  case strip_comb tm of
    (f, [a, b]) =>
      if is_const f andalso fst (dest_const f) = "STAR" then (f, a, b)
      else raise mk_HOL_ERR "wrappedEtherTransferScript" "dest_star" ""
  | _ => raise mk_HOL_ERR "wrappedEtherTransferScript" "dest_star" ""

fun strip_star tm =
  let val (_, a, b) = dest_star tm in strip_star a @ strip_star b end
  handle HOL_ERR _ => [tm]

(* the postcondition in the order SPEC_to_run_transaction names it *)
val transfer_spec_ordered =
  let
    val post = rand (concl transfer_spec_pool)
    val (star, _, _) = dest_star post
    fun mk_star (a, b) = list_mk_comb (star, [a, b])
    fun head_name tm =
      let val f = fst (strip_comb tm) in
        if is_const f then fst (dest_const f) else ""
      end
    val factors = strip_star post
    (* EIP-8037: `SPEC_to_run_transaction`'s Q names the frame's state-gas
       reservoir between its gas and its message parameters. *)
    val names = ["evm_Exception", "evm_ReturnData", "evm_Logs",
                 "evm_Rollback", "evm_Contexts", "evm_GasUsed",
                 "evm_StateGasLeft",
                 "evm_MsgParams", "evm_AddRefund", "evm_SubRefund",
                 "evm_TxParams"]
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
    CONV_RULE (RAND_CONV (REWR_CONV eq)) transfer_spec_pool
  end

val transfer_lift =
  let
    val th = MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                         SPEC_to_run_transaction) transfer_spec_ordered
    val (ants, _) = strip_imp (concl th)
    val (q, form) = dest_eq (last ants)
    val (tmS, tyS) = match_term form q
  in
    INST tmS (INST_TYPE tyS th) |> REWRITE_RULE [AND_IMP_INTRO]
  end

(* MATCH_MP primed the lifting theorem's states; name them s and s' *)
val transfer_lift =
  INST [var_named transfer_lift "s''" |-> mk_var ("s", “:execution_state”),
        var_named transfer_lift "s'''" |-> mk_var ("s'", “:execution_state”)]
    transfer_lift

Theorem transfer_value_zero[local]:
  transfer_value f t 0 = I
Proof
  rw[FUN_EQ_THM, transfer_value_def]
QED

Theorem transfer_value_enc[local]:
  enc (Tuple [Uint 256]) (ListV [NumV wad]) = word_to_bytes (n2w wad : bytes32) T
Proof
  simp[head_lengths_def, REV_DEF]
QED

Theorem access_slot_cost_le[local]:
  access_slot_cost rb a ≤ 2100
Proof
  rw[access_slot_cost_def, warm_access_cost_def, cold_sload_cost_def]
QED

Theorem accesses_add_slot_accounts[local]:
  (accesses_add_slot a rb).accounts = rb.accounts
Proof
  rw[accesses_add_slot_def]
QED

Theorem access_slot_cost_add_slot[local]:
  access_slot_cost (accesses_add_slot a rb) a = 100
Proof
  rw[access_slot_cost_def, accesses_add_slot_def, warm_access_cost_def]
QED

(* an SSTORE to a slot just read pays the warm access, not the cold one *)
Theorem SStore_gas_add_slot[local]:
  FST (SStore_gas original (accesses_add_slot (SK a k) rb) a k v) =
  sstore_base_gas (lookup_storage k (lookup_account a original).storage)
                  (lookup_storage k (lookup_account a rb.accounts).storage) v +
  warm_access_cost
Proof
  rw[SStore_gas_def, access_slot_cost_add_slot,
     warm_access_cost_def, accesses_add_slot_accounts]
  \\ pairarg_tac \\ gvs[]
QED

Theorem sstore_base_gas_le[local]:
  sstore_base_gas ov cv v ≤ storage_write_cost
Proof
  rw[sstore_base_gas_def, storage_write_cost_def, warm_access_cost_def]
QED

(* EIP-8038 prices the write itself, whether the slot was set or updated, so
   this is at most one `STORAGE_WRITE`, not the old
   `storage_update_cost - cold_sload_cost`; the slot's access is a separate
   term of the charge. *)
Theorem sstore_base_gas_same_le[local]:
  (c = 0w ⇒ v = c) ⇒
  sstore_base_gas c c v ≤ storage_write_cost
Proof
  rw[sstore_base_gas_def, storage_write_cost_def, warm_access_cost_def]
  \\ gvs[]
QED

(* EIP-8037's state-gas side of the two writes.

   The first write cannot create a slot: `wad` is bounded by the sender's
   balance, so a zero sender balance forces `wad = 0` and the write leaves
   the slot as it was.

   The second creates one exactly when the recipient's balance slot is
   zero, which is what the statement's hypothesis covers.  Its current
   value is read from the accounts the first write already touched, so the
   two lookups are not syntactically equal and the bound has to be stated
   for the general pair. *)
Theorem sstore_state_gas_sender[local]:
  wad ≤ w2n c ⇒ sstore_state_gas c c (-1w * n2w wad + c) = 0
Proof
  rw[sstore_state_gas_def]
  \\ Cases_on `c = 0w` \\ gvs[]
QED

Theorem sstore_state_gas_le_reservoir[local]:
  (ov = 0w ⇒ storage_set_state_gas ≤ sl) ⇒ sstore_state_gas ov cv v ≤ sl
Proof
  rw[sstore_state_gas_def]
  \\ Cases_on `ov = 0w` \\ gvs[]
  \\ Cases_on `ov = cv ∧ cv ≠ v` \\ gvs[]
QED

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

Theorem weth_transfer_run_transaction:
  (lookup_account addr accounts).code = contract_code ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "transfer" [Address; Uint 256] ++
     enc (Tuple [Address; Uint 256]) (ListV [NumV (w2n dst); NumV wad]))
    37162 s ∧
  wad ≤ w2n (lookup_storage (balance_slot_key tx.from)
               (lookup_account addr accounts).storage) ∧
  (* EIP-8037: a write that creates a slot charges its state gas to the
     frame's reservoir, and `SPEC_SStore`'s rule requires the reservoir to
     cover that charge -- a charge the reservoir cannot cover spills into
     execution gas, which the rule does not describe yet.  The transfer's
     first write never creates a slot (`wad` is bounded by the sender's
     balance, so a zero balance means a zero `wad`); the second creates one
     exactly when the recipient's balance slot is zero, which is when the
     reservoir has to hold a slot's worth of state gas. *)
  (lookup_storage (balance_slot_key dst)
     (lookup_account addr accounts).storage = 0w ⇒
   storage_set_state_gas ≤ s.txParams.stateGasReservoir) ∧
  access_slot_check dom (SK addr (balance_slot_key tx.from)) ∧
  access_slot_check dom (SK addr (balance_slot_key dst)) ∧
  blk.coinBase ≠ addr
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = enc (Tuple [Bool]) (ListV [NumV 1]) ∧
    result.logs =
      [<| logger := addr;
          topics :=
            [word_of_bytes_be
               (Keccak_256_string "Transfer(address,address,uint256)");
             w2w tx.from; w2w dst];
          data := enc (Tuple [Uint 256]) (ListV [NumV wad]) |>] ∧
    (∀a. a ≠ addr ⇒
         (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    lookup_account addr accounts' =
      let acc = lookup_account addr accounts;
          ks = balance_slot_key tx.from;
          kd = balance_slot_key dst;
          st = update_storage ks (lookup_storage ks acc.storage - n2w wad)
                 acc.storage
      in acc with storage :=
           update_storage kd (lookup_storage kd st + n2w wad) st
Proof
  PURE_REWRITE_TAC [cv_eval “enc (Tuple [Bool]) (ListV [NumV 1])”,
                    cv_eval “word_of_bytes_be (Keccak_256_string
                       "Transfer(address,address,uint256)") : bytes32”,
                    transfer_value_enc, zero_value_call_def]
  \\ strip_tac
  \\ strip_assume_tac contract_code_not_delegation
  \\ drule_all initial_state_call_code \\ strip_tac
  \\ drule initial_state_contract
  \\ disch_then (qspec_then `addr` mp_tac)
  \\ impl_tac >- gvs[]
  \\ strip_tac
  \\ fs[GSYM parsed_contract_code_def]
  \\ drule_all wf_initial_state \\ strip_tac
  \\ `∃rest. tx.data = [0xA9w; 0x05w; 0x9Cw; 0xBBw] ++
                       word_to_bytes (w2w dst : bytes32) T ++
                       word_to_bytes (n2w wad : bytes32) T ++ rest`
  by (qpat_x_assum `_ ≼ tx.data` mp_tac
      \\ rewrite_tac[transfer_selector_eq, transfer_args_enc, IS_PREFIX_APPEND]
      \\ strip_tac \\ simp[REV_DEF, w2w_def])
  \\ `wad < dimword (:256)`
  by (qspec_then `lookup_storage (balance_slot_key tx.from)
                    (lookup_account addr accounts).storage`
        assume_tac w2n_lt
      \\ decide_tac)
  \\ mp_tac (Q.INST [‘p’ |-> ‘ctxt.msgParams’, ‘rb’ |-> ‘s.rollback’,
                     ‘d’ |-> ‘dom’, ‘rd’ |-> ‘[]’, ‘l’ |-> ‘[]’,
                     ‘ar’ |-> ‘0’, ‘sr’ |-> ‘0’,
                     (* the outermost frame's own meter: the path carries it
                        through, and only the SSTORE's state gas moves it.  A
                        fresh frame has nothing spilled or committed.  `sl` is
                        the reservoir the SSTORE rule itself names. *)
                     ‘sg’ |-> ‘ctxt.stateGasLeft’,
                     ‘sl’ |-> ‘ctxt.stateGasLeft’,
                     ‘sp’ |-> ‘0’,
                     ‘bsl’ |-> ‘ctxt.stateGasBaseline’,
                     ‘cm’ |-> ‘0’,
                     ‘original’ |-> ‘s.originalAccounts’,
                     ‘txParams’ |-> ‘s.txParams’, ‘callee’ |-> ‘addr’,
                     ‘s'’ |-> ‘s with rollback updated_by
                       (λr. r with accounts updated_by
                              transfer_value tx.from addr tx.value)’]
                    transfer_lift)
  \\ impl_tac
  >- (
    simp_tac pure_ss [evm2set_def, GSYM STAR_ASSOC]
    \\ simp[STAR_evm2set, STAR_evm_OriginalAccounts, STAR_CODE_POOL_evm2set,
            cond_STAR, SEP_T_def,
            transfer_value_zero, execution_state_component_equality,
            rollback_state_component_equality, fmap_entries_def,
            (* EIP-7708: the frame's first log is the transaction's own
               transfer, which a zero-value call does not emit. *)
            transfer_log_def,
            SIMP_RULE std_ss [APPEND] transfer_selector_calldata,
            DROP_APPEND, DROP_LENGTH_TOO_LONG, calldata_word, mask_and_w2w,
            balance_slot_key_bytes]
    \\ simp[access_slot_cost_add_slot, SStore_gas_add_slot,
            accesses_add_slot_accounts]
    \\ qpat_assum `s.originalAccounts = _` (fn th => rewrite_tac[th])
    \\ qpat_assum `lookup_account addr s.rollback.accounts = _`
         (fn th => rewrite_tac[th])
    \\ qmatch_goalsub_abbrev_tac `sstore_base_gas c0 c0 v0`
    \\ `sstore_base_gas c0 c0 v0 ≤ storage_write_cost`
    by (irule sstore_base_gas_same_le \\ qunabbrevl_tac [`c0`, `v0`]
        \\ strip_tac \\ gvs[])
    \\ simp[warm_access_cost_def, storage_write_cost_def]
    \\ gas_bounds_tac
    (* EIP-8037: the path's remaining condition is what state gas the two
       writes create.  The first creates nothing (`sstore_state_gas_sender`),
       and the second's creation is what the statement's hypothesis puts
       inside the reservoir. *)
    \\ `FST (HD s.contexts) = ctxt`
         by (qpat_assum `s.contexts = _` (fn th => rewrite_tac[th])
             \\ simp[])
    \\ `ctxt.msgParams.caller = tx.from`
         by (qpat_assum `FST (HD s.contexts) = _`
               (fn th => rewrite_tac [GSYM th])
             \\ simp[])
    \\ `sstore_state_gas c0 c0 v0 = 0`
         by (qunabbrevl_tac [`c0`, `v0`]
             \\ irule sstore_state_gas_sender \\ simp[])
    \\ simp[SStore_state_gas_def]
    \\ qmatch_goalsub_abbrev_tac
         `sstore_state_gas (lookup_storage (balance_slot_key dst) _) ov0 vv0`
    \\ `sstore_state_gas (lookup_storage (balance_slot_key dst)
                            (lookup_account ctxt.msgParams.callee accounts).storage)
            ov0 vv0 ≤ ctxt.stateGasLeft`
         by (irule sstore_state_gas_le_reservoir \\ strip_tac
             \\ Cases_on `lookup_storage (balance_slot_key dst)
                           (lookup_account ctxt.msgParams.callee accounts).storage = 0w`
             \\ gvs[])
    \\ gvs[call_stipend_def, SStore_state_gas_def,
           sstore_state_gas_refund_def]
    (* EIP-8037: the two writes' state-gas refunds are the last `if`s in the
       goal.  Splitting them lets the arithmetic close on the reservoir bound
       the facts above give; the sender's refund condition is contradictory
       (`c0 ≠ v0 ∧ c0 = v0`), so that branch is empty. *)
    (* the bounds left are `storage_write_cost + warm_access_cost`, which the
       arithmetic needs as numbers *)
    \\ rpt (IF_CASES_TAC
            \\ gvs[warm_access_cost_def, storage_write_cost_def]))
  \\ strip_tac
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ qpat_assum `∀a. lookup_account a accounts' = _`
       (qspec_then `addr` assume_tac)
  \\ gvs[SStore_write_def, sstore_write_accounts_updater_def,
         accesses_add_slot_def, lookup_account_def, update_account_def,
         APPLY_UPDATE_THM, calldata_word, mask_and_w2w,
         DROP_APPEND, DROP_LENGTH_TOO_LONG, balance_slot_key_bytes]
  (* the accounting wraps the accounts in `clear_deleted` now, and this
     transaction deletes nothing, so it comes straight back off -- after the
     definitions above, which are heavy enough as it is *)
  \\ gvs[clear_deleted_def]
  \\ simp[REVERSE_word_to_bytes_bytes32]
  \\ qmatch_goalsub_abbrev_tac `cc * n2w wad + _`
  \\ `cc * n2w wad = -n2w wad`
  by (`cc = -1w` by (qunabbrev_tac `cc` \\ EVAL_TAC)
      \\ pop_assum SUBST1_TAC \\ MATCH_ACCEPT_TAC (GSYM WORD_NEG_MUL))
  \\ `-n2w wad : bytes32 = n2w ((dimword (:256) − wad) MOD dimword (:256))`
  by (rewrite_tac[word_2comp_n2w] \\ gvs[n2w_11])
  \\ qpat_x_assum `cc * _ = _` SUBST1_TAC
  \\ qpat_x_assum `-n2w wad = _`
       (SUBST1_TAC o REWRITE_RULE [EVAL “dimword (:256)”])
  \\ simp[account_state_component_equality]
  \\ rw[FUN_EQ_THM]
QED

Theorem balance_slot_lookup[local]:
  (∀a. balance_slot_key a ∉ {0w; 1w; 2w} ∧
       (a ∈ ts ∨ balance_slot_key a ∉ IMAGE balance_slot_key ts) ⇒
       lookup_storage (balance_slot_key a) st = n2w (f a)) ⇒
  ∀x. balance_slot_key x ∉ {0w; 1w; 2w} ∧
      (∀b. b ∈ ts ∧ balance_slot_key x = balance_slot_key b ⇒ x = b) ⇒
      lookup_storage (balance_slot_key x) st = n2w (f x)
Proof
  rpt strip_tac \\ first_x_assum irule \\ simp[] \\ metis_tac[]
QED

Theorem lookup_update_storage[local]:
  lookup_storage k (update_storage k' v s) =
  if k' = k then v else lookup_storage k s
Proof
  rw[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
QED

Theorem WETH_transfer_locked[local]:
  (WETH_transfer src dst n ws).locked = ws.locked
Proof
  rw[WETH_transfer_def]
QED

Theorem WETH_transfer_fields[local]:
  (WETH_transfer src dst n ws).touched = dst INSERT ws.touched ∧
  (WETH_transfer src dst n ws).balances =
    (dst =+ (src =+ ws.balances src - n) ws.balances dst + n)
      ((src =+ ws.balances src - n) ws.balances)
Proof
  rw[WETH_transfer_def]
QED

(* the storage writes of a transfer keep the WETH_EVM relation *)
Theorem WETH_transfer_storage[local]:
  wf_WETH_state ws ∧ wad ≤ ws.balances src ∧
  (∀a. balance_slot_key a ∉ {0w; 1w; 2w} ∧
       (a ∈ ws.touched ∨ balance_slot_key a ∉ IMAGE balance_slot_key ws.touched) ⇒
       lookup_storage (balance_slot_key a) st = n2w (ws.balances a)) ∧
  (∀a b. (a = src ∨ a = dst) ∧
         (b = src ∨ b = dst ∨ b ∈ ws.touched) ∧
         balance_slot_key a = balance_slot_key b ⇒ a = b) ∧
  balance_slot_key src ∉ {0w; 1w; 2w} ∧
  balance_slot_key dst ∉ {0w; 1w; 2w}
  ⇒
  let st1 = update_storage (balance_slot_key src)
              (n2w (ws.balances src - wad)) st;
      st2 = update_storage (balance_slot_key dst)
              (lookup_storage (balance_slot_key dst) st1 + n2w wad) st1;
      ws' = WETH_transfer src dst wad ws in
  wf_WETH_state ws' ∧
  (∀a. balance_slot_key a ∉ {0w; 1w; 2w} ∧
       (a ∈ ws'.touched ∨
        balance_slot_key a ∉ IMAGE balance_slot_key ws'.touched) ⇒
       lookup_storage (balance_slot_key a) st2 = n2w (ws'.balances a)) ∧
  lookup_storage 0w st2 = lookup_storage 0w st ∧
  lookup_storage 1w st2 = lookup_storage 1w st ∧
  lookup_storage 2w st2 = lookup_storage 2w st
Proof
  strip_tac
  \\ `∀a. a ∉ ws.touched ⇒ ws.balances a = 0`
     by (gvs[wf_WETH_state_def, SUBSET_DEF] \\ metis_tac[NOT_ZERO_LT_ZERO])
  \\ `lookup_storage (balance_slot_key src) st = n2w (ws.balances src) ∧
      lookup_storage (balance_slot_key dst) st = n2w (ws.balances dst)`
     by (conj_tac \\ first_assum irule \\ simp[] \\ metis_tac[])
  \\ `balance_slot_key src = balance_slot_key dst ⇒ src = dst`
     by metis_tac[]
  \\ rpt (qpat_x_assum `balance_slot_key _ ∉ _`
            (strip_assume_tac o
             REWRITE_RULE [IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM]))
  \\ simp_tac std_ss [LET_THM]
  \\ conj_tac >- (irule wf_WETH_transfer \\ asm_rewrite_tac[])
  \\ asm_rewrite_tac[lookup_update_storage, WETH_transfer_fields,
                     APPLY_UPDATE_THM]
  \\ rpt gen_tac \\ disch_then (map_every assume_tac o CONJUNCTS)
  \\ Cases_on `a = src`
  >- (
    pop_assum SUBST_ALL_TAC
    \\ Cases_on `src = dst`
    >- (pop_assum SUBST_ALL_TAC \\ rewrite_tac[word_add_n2w]
        \\ qpat_assum `wad ≤ _` (rewrite_tac o single o MATCH_MP SUB_ADD))
    \\ `dst ≠ src ∧ balance_slot_key dst ≠ balance_slot_key src`
       by metis_tac[]
    \\ asm_rewrite_tac[])
  \\ Cases_on `a = dst`
  >- (
    pop_assum SUBST_ALL_TAC
    \\ `src ≠ dst ∧ balance_slot_key src ≠ balance_slot_key dst`
       by metis_tac[]
    \\ asm_rewrite_tac[word_add_n2w])
  \\ `src ≠ a ∧ dst ≠ a` by metis_tac[]
  \\ `balance_slot_key dst ≠ balance_slot_key a`
     by metis_tac[IN_IMAGE, IN_INSERT]
  \\ asm_rewrite_tac[]
  \\ Cases_on `balance_slot_key src = balance_slot_key a`
  >- (
    `src ∉ ws.touched ∧ a ∉ ws.touched`
      by metis_tac[IN_IMAGE, IN_INSERT]
    \\ `ws.balances src = 0 ∧ ws.balances a = 0` by metis_tac[]
    \\ `wad = 0` by decide_tac
    \\ asm_rewrite_tac[SUB_0])
  \\ asm_rewrite_tac[]
  \\ qpat_assum `∀a. _ ∧ _ ⇒ lookup_storage _ st = _` irule
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ metis_tac[IN_IMAGE, IN_INSERT]
QED

(* the same from the WETH_EVM relation: the abstract state moves wad from
   the caller to dst, assuming the two balance slots involved don't collide
   with each other, with any touched account's slot, or with slots 0-2 *)
Theorem WETH_EVM_transfer_run_transaction:
  WETH_EVM addr ws accounts ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "transfer" [Address; Uint 256] ++
     enc (Tuple [Address; Uint 256]) (ListV [NumV (w2n dst); NumV wad]))
    37162 s ∧
  wad ≤ ws.balances tx.from ∧
  (lookup_storage (balance_slot_key dst)
     (lookup_account addr accounts).storage = 0w ⇒
   storage_set_state_gas ≤ s.txParams.stateGasReservoir) ∧
  (∀a b. (a = tx.from ∨ a = dst) ∧
         (b = tx.from ∨ b = dst ∨ b ∈ ws.touched) ∧
         balance_slot_key a = balance_slot_key b ⇒ a = b) ∧
  balance_slot_key tx.from ∉ {0w; 1w; 2w} ∧
  balance_slot_key dst ∉ {0w; 1w; 2w} ∧
  access_slot_check dom (SK addr (balance_slot_key tx.from)) ∧
  access_slot_check dom (SK addr (balance_slot_key dst)) ∧
  blk.coinBase ≠ addr
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = enc (Tuple [Bool]) (ListV [NumV 1]) ∧
    result.logs =
      [<| logger := addr;
          topics :=
            [word_of_bytes_be
               (Keccak_256_string "Transfer(address,address,uint256)");
             w2w tx.from; w2w dst];
          data := enc (Tuple [Uint 256]) (ListV [NumV wad]) |>] ∧
    (∀a. a ≠ addr ⇒
         (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    WETH_EVM addr (WETH_transfer tx.from dst wad ws) accounts'
Proof
  strip_tac
  \\ qpat_x_assum `WETH_EVM _ _ _`
       (strip_assume_tac o SIMP_RULE std_ss [WETH_EVM_def, LET_THM])
  \\ qpat_assum `wf_WETH_state ws`
       (strip_assume_tac o REWRITE_RULE [wf_WETH_state_def])
  \\ qpat_assum `∀a. _ ∧ _ ⇒ lookup_storage _ _ = n2w _`
       (assume_tac o MATCH_MP balance_slot_lookup)
  \\ `lookup_storage (balance_slot_key tx.from)
        (lookup_account addr accounts).storage = n2w (ws.balances tx.from) ∧
      lookup_storage (balance_slot_key dst)
        (lookup_account addr accounts).storage = n2w (ws.balances dst)`
  by (pop_assum (fn th => conj_tac \\ irule th)
      \\ asm_rewrite_tac[] \\ rpt strip_tac
      \\ qpat_x_assum `∀a b. _` irule \\ asm_rewrite_tac[])
  \\ `wad ≤ w2n (lookup_storage (balance_slot_key tx.from)
                   (lookup_account addr accounts).storage)`
  by (qpat_assum `lookup_storage (balance_slot_key tx.from) _ = _`
        SUBST1_TAC
      \\ `ws.balances tx.from MOD dimword (:256) = ws.balances tx.from`
      by (irule LESS_MOD
          \\ rewrite_tac[EVAL “dimword (:256)”, GSYM (EVAL “2n ** 256”)]
          \\ qpat_assum `∀a. ws.balances a < _` MATCH_ACCEPT_TAC)
      \\ asm_rewrite_tac[w2n_n2w])
  \\ drule_at_then Any (drule_all_then strip_assume_tac)
       weth_transfer_run_transaction
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ asm_rewrite_tac[WETH_EVM_def]
  \\ qpat_x_assum `lookup_account addr accounts' = _` SUBST1_TAC
  \\ simp_tac std_ss [LET_THM]
  \\ qpat_assum `lookup_storage (balance_slot_key tx.from) _ = _`
       (fn th => rewrite_tac[th])
  \\ qpat_assum `wad ≤ ws.balances tx.from`
       (rewrite_tac o single o GSYM o MATCH_MP n2w_sub)
  \\ mp_tac (Q.INST [`src` |-> `tx.from`,
                     `st` |-> `(lookup_account addr accounts).storage`]
                    WETH_transfer_storage)
  \\ impl_tac >- asm_rewrite_tac[]
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ asm_rewrite_tac[account_state_accfupds, K_THM, WETH_transfer_locked]
QED
