(* WETH's name() getter, from the block summaries of wrappedEtherTheory
   composed along its path and lifted to run_transaction. *)
Theory wrappedEtherName
Ancestors
  arithmetic list rich_list combin pair pred_set byte cv_std words
  vfmTypes vfmConstants vfmState vfmContext vfmExecution vfmExecutionProp
  vfmBuffer
  set_sep prog vfmProg contractABI wrappedEther
Libs
  dep_rewrite wordsLib cv_transLib evmDecompLib

Theorem contract_code_not_delegation:
  ¬NULL contract_code ∧ ¬is_delegation contract_code
Proof
  `LENGTH contract_code ≠ 0 ∧ LENGTH contract_code ≠ 23`
  by (rewrite_tac[cv_eval “LENGTH contract_code”] \\ simp[])
  \\ rw[is_delegation_def, NULL_LENGTH]
QED

(* ---------------------------------------------------------------- *)
(* Calldata starting with name()'s selector *)

Theorem name_selector_eq:
  function_selector "name" [] = [0x06w; 0xFDw; 0xDEw; 0x03w]
Proof
  CONV_TAC (LAND_CONV cv_eval) \\ rw[]
QED

Theorem name_selector_calldata:
  0xFFFFFFFFw &&
  word_of_bytes F 0w
    (REVERSE (take_pad_0 32 ([0x06w; 0xFDw; 0xDEw; 0x03w] ++ rest))) //
  (0x100000000000000000000000000000000000000000000000000000000w : bytes32)
  = 0x6FDDE03w
Proof
  qabbrev_tac `sel = [0x06w; 0xFDw; 0xDEw; 0x03w] : word8 list`
  \\ `∃r. take_pad_0 32 (sel ++ rest) = sel ++ r ∧ LENGTH r = 28`
  by rw[take_pad_0_def, TAKE_APPEND, PAD_RIGHT, Abbr`sel`, LENGTH_TAKE_EQ]
  \\ simp[GSYM word_of_bytes_le_def]
  \\ DEP_REWRITE_TAC[word_of_bytes_le_eq_num_of_bytes]
  \\ simp[REVERSE_APPEND, num_of_bytes_APPEND, word_div_def]
  \\ qspec_then `REVERSE r` assume_tac num_of_bytes_lt
  \\ `num_of_bytes (REVERSE sel) = 0x6FDDE03`
  by simp[Abbr`sel`, num_of_bytes_def, dimword_8]
  \\ gvs[]
  \\ `num_of_bytes (REVERSE r) + 256 ** 28 * 0x6FDDE03 < dimword (:256)`
  by simp[]
  \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ qmatch_goalsub_abbrev_tac `(a + b) DIV c`
  \\ `a < c` by simp[Abbr`a`, Abbr`c`]
  \\ `(a + b) DIV c = 117300739`
  by (`a + b = 117300739 * c + a` by simp[Abbr`b`, Abbr`c`]
      \\ pop_assum SUBST1_TAC
      \\ simp[ADD_DIV_ADD_DIV, LESS_DIV_EQ_ZERO, Abbr`c`])
  \\ simp[]
QED

(* ---------------------------------------------------------------- *)
(* The name() path, composed from the block summaries *)

fun weth_block n v =
  DB.fetch "wrappedEther" ("weth_block_" ^ Int.toString n ^ v)

(* the selector chain, the callvalue check, the getter at 1245 taking the
   short-string branch, the ABI encoder with its copy loop run once *)
val name_path =
  [(0, "_skip"), (13, "_take"), (185, "_take"), (196, "_Jump"),
   (1245, "_skip"), (1325, "_skip"), (1333, "_Jump"), (1395, "_Jump"),
   (204, ""), (241, "_skip"), (250, "_Jump"), (241, "_take"),
   (268, "_skip"), (288, ""), (313, "_outermost")]

val slot0_word =
  “0x577261707065642045746865720000000000000000000000000000000000001Aw
   : bytes32”

(* slot 0 holds "Wrapped Ether" as a short string: with it the getter's
   branches are decided; the composed path keeps it as a side condition *)
val slot0 = ASSUME (mk_eq (“lookup_storage 0w
  (lookup_account (p:message_parameters).callee
     (rb:rollback_state).accounts).storage”, slot0_word))

val memory_cost_64_32 =
  Q.SPECL [`64`,`32`] (Q.GENL [`off`,`sz`] memory_cost_offset_to_0)
  |> SIMP_RULE arith_ss []

(* evaluates ground with_zero and word_div applications, which the
   simplifier leaves alone; used while composing, removed after *)
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

val name_config : evmDecompLib.config =
  {code_eq = contract_code_eq, parsed_eq = parsed_contract_code_eq,
   hints = [],
   simps = [with_zero_def, mask_and_w2w, memory_cost_64_32, slot0,
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

(* composed one summary at a time, from an empty memory and no gas used *)
val name_path_composed =
  let
    val ths = map (fn (n, v) => inline_memory (weth_block n v)) name_path
    val th0 = hd ths
    val th0 = INST [var_named th0 "m" |-> “empty_buffer”,
                    var_named th0 "g" |-> “0n”] th0
  in
    List.foldl (fn (th, acc) => compose_blocks name_config [acc, th])
      th0 (tl ths)
  end

(* ground_div is only for the composition *)
val () = diminish_srw_ss ["ground_div"]

(* the path keeps slot0 as a condition, not as an assumption *)
val () = if null (hyp name_path_composed) then ()
         else raise mk_HOL_ERR "wrappedEtherNameScript" "name_path_composed"
                "hypotheses"

(* a call's start: no pending exception or jump, no outer contexts, an
   empty stack, and not a create, so no code deposit *)
val name_spec_start =
  let
    val th = name_path_composed
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

(* evaluates the closed numbers and byte lists: the memory costs and the
   returned bytes *)
fun ground_conv tm =
  if null (free_vars tm) andalso not (is_const tm) andalso
     not (numSyntax.is_numeral tm) andalso
     (type_of tm = numSyntax.num orelse
      (type_of tm = “:word8 list” andalso
       not (listSyntax.is_list tm andalso
            List.all wordsSyntax.is_word_literal
              (fst (listSyntax.dest_list tm)))))
  then
    let
      val th = cv_eval tm handle Interrupt => raise Interrupt | _ =>
        ((REWRITE_CONV [expanded_memory_def, memory_expand_by_def]
          THENC cv_eval) tm
         handle Interrupt => raise Interrupt | _ => EVAL tm)
    in
      if rhs (concl th) ~~ tm then NO_CONV tm else th
    end
  else NO_CONV tm

val name_spec_eval = CONV_RULE (TOP_SWEEP_CONV ground_conv) name_spec_start

Theorem FST_SND_SND_EVM_MODEL[local]:
  FST (SND (SND EVM_MODEL)) = EVM_INSTR
Proof
  rw[EVM_MODEL_def]
QED

(* ---------------------------------------------------------------- *)
(* Lifting the path to run_transaction *)

fun evc tm = tm |> (REWRITE_CONV [parsed_contract_code_eq] THENC EVAL)

(* the path's instructions are entries of the parsed code *)
val name_spec_code =
  let
    val th = MATCH_MP SPEC_SUBSET_CODE name_spec_eval
             |> SPEC “fmap_entries parsed_contract_code”
    val tac = rewrite_tac [SUBSET_DEF] \\ Cases
      \\ rewrite_tac [IN_INSERT, NOT_IN_EMPTY, PAIR_EQ]
      \\ strip_tac \\ rpt BasicProvers.VAR_EQ_TAC
      \\ simp [fmap_entries_def] \\ CONV_TAC evc
    val sub = prove (fst (dest_imp (concl th)), tac)
  in
    MP th sub
  end

(* framed with the components run_transaction's lifting names, the code
   moved into the pre- and postcondition *)
val name_spec_pool =
  SPEC “evm_Logs logs * evm_AddRefund addRefund * evm_SubRefund subRefund *
        evm_TxParams txParams * SEP_T”
    (MATCH_MP SPEC_FRAME name_spec_code)
  |> ONCE_REWRITE_RULE [GSYM SPEC_CODE]
  |> REWRITE_RULE [FST_SND_SND_EVM_MODEL]

fun dest_star tm =
  case strip_comb tm of
    (f, [a, b]) =>
      if is_const f andalso fst (dest_const f) = "STAR" then (f, a, b)
      else raise mk_HOL_ERR "wrappedEtherNameScript" "dest_star" ""
  | _ => raise mk_HOL_ERR "wrappedEtherNameScript" "dest_star" ""

fun strip_star tm =
  let val (_, a, b) = dest_star tm in strip_star a @ strip_star b end
  handle HOL_ERR _ => [tm]

(* the postcondition in the order SPEC_to_run_transaction names it *)
val name_spec_ordered =
  let
    val post = rand (concl name_spec_pool)
    val (star, _, _) = dest_star post
    fun mk_star (a, b) = list_mk_comb (star, [a, b])
    fun head_name tm =
      let val f = fst (strip_comb tm) in
        if is_const f then fst (dest_const f) else ""
      end
    val factors = strip_star post
    val names = ["evm_Exception", "evm_ReturnData", "evm_Logs",
                 "evm_Rollback", "evm_Contexts", "evm_GasUsed",
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
    CONV_RULE (RAND_CONV (REWR_CONV eq)) name_spec_pool
  end

val name_lift =
  let
    val th = MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                         SPEC_to_run_transaction) name_spec_ordered
    val (ants, _) = strip_imp (concl th)
    val (q, form) = dest_eq (last ants)
    val (tmS, tyS) = match_term form q
  in
    INST tmS (INST_TYPE tyS th) |> REWRITE_RULE [AND_IMP_INTRO]
  end

(* MATCH_MP primed the lifting theorem's states; name them s and s' *)
val name_lift =
  INST [var_named name_lift "s''" |-> mk_var ("s", “:execution_state”),
        var_named name_lift "s'''" |-> mk_var ("s'", “:execution_state”)]
    name_lift

Theorem transfer_value_zero[local]:
  transfer_value f t 0 = I
Proof
  rw[FUN_EQ_THM, transfer_value_def]
QED

Theorem weth_name_run_transaction:
  (lookup_account addr accounts).code = contract_code ∧
  lookup_storage 0w (lookup_account addr accounts).storage =
    0x577261707065642045746865720000000000000000000000000000000000001Aw ∧
  wf_accounts accounts ∧ ¬fIN addr precompile_addresses ∧
  tx.to = SOME addr ∧ tx.value = 0 ∧
  function_selector "name" [] ≼ tx.data ∧
  access_slot_check dom (SK addr 0w) ∧
  initial_state dom F chainId prevHashes blk accounts tx = SOME s ∧
  3110 ≤ (FST (HD s.contexts)).msgParams.gasLimit
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output =
      enc (Tuple [String]) (ListV [BytesV (MAP (n2w o ORD) "Wrapped Ether")]) ∧
    result.logs = [] ∧
    ∀a. (lookup_account a accounts').code =
        (lookup_account a s.rollback.accounts).code ∧
        (lookup_account a accounts').storage =
        (lookup_account a s.rollback.accounts).storage ∧
        (lookup_account a accounts').nonce =
        (lookup_account a s.rollback.accounts).nonce
Proof
  PURE_REWRITE_TAC [cv_eval “enc (Tuple [String])
                       (ListV [BytesV (MAP (n2w o ORD) "Wrapped Ether")])”]
  \\ strip_tac
  \\ strip_assume_tac contract_code_not_delegation
  \\ drule_all initial_state_call_code \\ strip_tac
  \\ fs[GSYM parsed_contract_code_def]
  \\ drule_all wf_initial_state \\ strip_tac
  \\ `∃rest. tx.data = [0x06w; 0xFDw; 0xDEw; 0x03w] ++ rest`
  by gvs[name_selector_eq, IS_PREFIX_APPEND]
  \\ mp_tac (Q.INST [‘p’ |-> ‘ctxt.msgParams’, ‘rb’ |-> ‘s.rollback’,
                     ‘d’ |-> ‘dom’, ‘rd’ |-> ‘[]’, ‘logs’ |-> ‘[]’,
                     ‘addRefund’ |-> ‘0’, ‘subRefund’ |-> ‘0’,
                     ‘txParams’ |-> ‘s.txParams’, ‘callee’ |-> ‘addr’,
                     ‘s'’ |-> ‘s with rollback updated_by
                       (λr. r with accounts updated_by
                              transfer_value tx.from addr tx.value)’]
                    name_lift)
  \\ impl_tac
  >- (
    simp_tac pure_ss [evm2set_def, GSYM STAR_ASSOC]
    \\ simp[STAR_evm2set, STAR_CODE_POOL_evm2set, cond_STAR, SEP_T_def,
            transfer_value_zero, execution_state_component_equality,
            rollback_state_component_equality,
            fmap_entries_def,
            SIMP_RULE std_ss [APPEND] name_selector_calldata]
    \\ `LENGTH rest + 4 ≤ 16777216 ∧ 3110 ≤ ctxt.msgParams.gasLimit` by gvs[]
    \\ `(LENGTH rest + 4) MOD dimword (:256) = LENGTH rest + 4`
    by (irule LESS_MOD \\ simp[dimword_def])
    \\ gvs[ADD1, dimword_def]
    \\ rw[access_slot_cost_def, accesses_add_slot_def, warm_access_cost_def,
          cold_sload_cost_def])
  \\ strip_tac
  \\ gvs[accesses_add_slot_def]
QED

(* the same from the WETH_EVM relation, which fixes code and slot 0 *)
Theorem WETH_EVM_name_run_transaction:
  WETH_EVM addr ws accounts ∧
  wf_accounts accounts ∧ ¬fIN addr precompile_addresses ∧
  tx.to = SOME addr ∧ tx.value = 0 ∧
  function_selector "name" [] ≼ tx.data ∧
  access_slot_check dom (SK addr 0w) ∧
  initial_state dom F chainId prevHashes blk accounts tx = SOME s ∧
  3110 ≤ (FST (HD s.contexts)).msgParams.gasLimit
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output =
      enc (Tuple [String]) (ListV [BytesV (MAP (n2w o ORD) "Wrapped Ether")]) ∧
    result.logs = [] ∧
    ∀a. (lookup_account a accounts').code =
        (lookup_account a s.rollback.accounts).code ∧
        (lookup_account a accounts').storage =
        (lookup_account a s.rollback.accounts).storage ∧
        (lookup_account a accounts').nonce =
        (lookup_account a s.rollback.accounts).nonce
Proof
  strip_tac
  \\ qpat_x_assum `WETH_EVM _ _ _`
       (strip_assume_tac o SIMP_RULE std_ss [WETH_EVM_def, LET_THM])
  \\ drule_all weth_name_run_transaction
  \\ disch_then ACCEPT_TAC
QED
