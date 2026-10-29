(* Read-only WETH entry points over run_transaction. *)
Theory wrappedEtherGetters
Ancestors
  arithmetic list rich_list combin pair pred_set byte cv_std words
  vfmTypes vfmConstants vfmState vfmContext vfmExecution vfmExecutionProp
  vfmBuffer set_sep prog vfmProg contractABI wrappedEther wrappedEtherName
  wrappedEtherTransfer
Libs
  dep_rewrite wordsLib cv_transLib evmDecompLib

Theorem getter_address_enc[local]:
  enc (Tuple [Address]) (ListV [NumV (w2n a)]) =
    word_to_bytes (w2w (a:address) : bytes32) T ∧
  enc (Tuple [Address; Address])
    (ListV [NumV (w2n owner); NumV (w2n spender)]) =
    word_to_bytes (w2w (owner:address) : bytes32) T ++
    word_to_bytes (w2w (spender:address) : bytes32) T
Proof
  simp[head_lengths_def, w2w_def, REV_DEF]
QED

Theorem getter_allowance_key[local]:
  word_of_bytes_be (Keccak_256_w64
    (word_to_bytes (w2w (spender:address) : bytes32) T ++
     word_to_bytes
       (word_of_bytes_be (Keccak_256_w64
         (word_to_bytes (w2w (owner:address) : bytes32) T ++
          word_to_bytes (4w:bytes32) T)) : bytes32) T)) =
  allowance_slot_key owner spender
Proof
  rewrite_tac[allowance_slot_key_def, word_to_bytes_le_def,
              REVERSE_word_to_bytes_bytes32]
QED

Theorem getter_balance_key[local]:
  word_of_bytes_be (Keccak_256_w64
    (word_to_bytes (w2w (a:address) : bytes32) T ++
     word_to_bytes (3w:bytes32) T)) = balance_slot_key a
Proof
  rewrite_tac[balance_slot_key_def, balance_slot_word_def,
              word_to_bytes_le_def, REVERSE_word_to_bytes_bytes32]
QED

Theorem getter_argument_reads[local]:
  LENGTH (sel:word8 list) = 4 ⇒
  word_of_bytes F 0w (REVERSE (take_pad_0 32
    (DROP 4 (sel ++ word_to_bytes (a:bytes32) T ++ rest)))) = a ∧
  word_of_bytes F 0w (REVERSE (take_pad_0 32
    (DROP 36 (sel ++ word_to_bytes a T ++ word_to_bytes (b:bytes32) T ++ rest)))) = b
Proof
  strip_tac
  >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, calldata_word]
QED

Theorem getter_bounds[local]:
  WETH_EVM addr ws accounts ⇒
  ws.locked < 2 ** 256 ∧
  (∀a. ws.balances a < 2 ** 256) ∧
  (∀owner spender. ws.allowances owner spender < 2 ** 256)
Proof
  simp[WETH_EVM_def, LET_THM, wf_WETH_state_def]
QED

Theorem getter_selectors[local]:
  function_selector "symbol" [] = [0x95w; 0xD8w; 0x9Bw; 0x41w] ∧
  function_selector "decimals" [] = [0x31w; 0x3Cw; 0xE5w; 0x67w] ∧
  function_selector "totalSupply" [] = [0x18w; 0x16w; 0x0Dw; 0xDDw] ∧
  function_selector "balanceOf" [Address] = [0x70w; 0xA0w; 0x82w; 0x31w] ∧
  function_selector "allowance" [Address; Address] = [0xDDw; 0x62w; 0xEDw; 0x3Ew]
Proof
  CONV_TAC cv_eval >> rw[]
QED

Theorem getter_selector_calldata[local]:
  LENGTH (sel:word8 list) = 4 ⇒
  0xFFFFFFFFw &&
  word_of_bytes F 0w (REVERSE (take_pad_0 32 (sel ++ rest))) //
    (0x100000000000000000000000000000000000000000000000000000000w : bytes32)
  = n2w (num_of_bytes (REVERSE sel))
Proof
  strip_tac
  >> `∃r. take_pad_0 32 (sel ++ rest) = sel ++ r ∧ LENGTH r = 28`
     by (rw[take_pad_0_def, TAKE_APPEND, PAD_RIGHT, LENGTH_TAKE_EQ,
            TAKE_LENGTH_TOO_LONG]
         >> qexists_tac `TAKE 28 rest ++ REPLICATE (28 - LENGTH rest) 0w`
         >> simp[LENGTH_TAKE_EQ])
  >> simp[GSYM word_of_bytes_le_def]
  >> DEP_REWRITE_TAC[word_of_bytes_le_eq_num_of_bytes]
  >> simp[REVERSE_APPEND, num_of_bytes_APPEND, word_div_def]
  >> qspec_then `REVERSE r` assume_tac num_of_bytes_lt
  >> qspec_then `REVERSE sel` assume_tac num_of_bytes_lt
  >> gvs[]
  >> `num_of_bytes (REVERSE r) + 256 ** 28 * num_of_bytes (REVERSE sel)
        < dimword (:256)` by simp[]
  >> simp[]
  >> conj_tac >- EVAL_TAC
  >> `num_of_bytes (REVERSE r) + 256 ** 28 * num_of_bytes (REVERSE sel) =
        num_of_bytes (REVERSE sel) * 256 ** 28 + num_of_bytes (REVERSE r)`
     by metis_tac[ADD_COMM, MULT_COMM]
  >> pop_assum SUBST1_TAC
  >> simp[ADD_DIV_ADD_DIV, LESS_DIV_EQ_ZERO]
  >> `n2w (num_of_bytes (REVERSE sel)) : bytes32 =
        w2w (n2w (num_of_bytes (REVERSE sel)) : word32)`
     by simp[w2w_def, w2n_n2w, dimword_def]
  >> pop_assum SUBST1_TAC >> blastLib.BBLAST_TAC
QED

Theorem getter_call_balance[local]:
  WETH_EVM addr ws accounts ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr data gas s ⇒
  (lookup_account addr s.rollback.accounts).balance = ws.locked
Proof
  simp[zero_value_call_def, WETH_EVM_def, LET_THM]
  >> strip_tac
  >> qpat_x_assum `initial_state _ _ _ _ _ _ _ = _` mp_tac
  >> simp[initial_state_def, CaseEq "option"] >> strip_tac
  >> pairarg_tac >> gvs[]
  >> pairarg_tac >> gvs[CaseEq "option"]
  >> `lookup_account addr postAuthAccounts = lookup_account addr accounts'`
     by (drule pre_transaction_updates_contract
         >> disch_then (qspec_then `addr` strip_assume_tac)
         >> drule process_authorizations_contract
         >> disch_then (qspec_then `addr` mp_tac)
         >> simp[contract_code_not_delegation])
  >> gvs[initial_rollback_def]
  >> qpat_x_assum `pre_transaction_updates _ _ _ = _` mp_tac
  >> simp[pre_transaction_updates_def, CaseEq "bool"] >> strip_tac
  >> `tx.from ≠ addr` by metis_tac[contract_code_not_delegation]
  >> gvs[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

Theorem getter_word_output[local]:
  n < 2 ** 256 ⇒
  REVERSE (word_to_bytes (n2w n : bytes32) F) =
    enc (Tuple [Uint 256]) (ListV [NumV n])
Proof
  simp[REVERSE_word_to_bytes_bytes32, head_lengths_def, REV_DEF]
QED

Theorem getter_decimals_output[local]:
  REVERSE (word_to_bytes (255w && (18w:bytes32)) F) =
    enc (Tuple [Uint 8]) (ListV [NumV 18])
Proof
  EVAL_TAC
QED

Theorem getter_access_gas[local]:
  access_slot_cost rb k ≤ 2100 ∧ Balance_gas rb addr ≤ 2600
Proof
  simp[access_slot_cost_def, Balance_gas_def, warm_access_cost_def,
       cold_sload_cost_def, access_cost_def, cold_access_cost_def,
       vfmOperationTheory.static_gas_def]
  >> conj_tac >> IF_CASES_TAC >> simp[]
QED

Theorem getter_warm_slot_gas[local]:
  access_slot_cost (accesses_add_slot k rb) k = 100
Proof
  simp[access_slot_cost_def, accesses_add_slot_def, warm_access_cost_def]
QED

Theorem getter_path_gas_bounds[local]:
  9 + (Balance_gas rb addr + 234) <= 4000 /\
  9 + (access_slot_cost rb k + 335) <= 4000 /\
  9 + (42 + (access_slot_cost rb k + 383)) <= 4000 /\
  9 + (42 + (42 + (access_slot_cost rb k + 524))) <= 4000 /\
  9 + (access_slot_cost rb k +
    (3 + (2 * access_slot_cost (accesses_add_slot k rb) k + 952))) <= 4000
Proof
  strip_assume_tac getter_access_gas
  >> simp[getter_warm_slot_gas]
QED

Theorem getter_account_frame[local]:
  (accesses_add_slot k rb).accounts = rb.accounts /\
  (accesses_add addr rb).accounts = rb.accounts
Proof
  simp[accesses_add_slot_def, accesses_add_def]
QED

fun weth_block n v =
  DB.fetch "wrappedEther" ("weth_block_" ^ Int.toString n ^ v)

val getter_memory_cost_64_32 =
  Q.SPECL [`64`,`32`] (Q.GENL [`off`,`sz`] memory_cost_offset_to_0)
  |> SIMP_RULE arith_ss []

fun getter_config extra : evmDecompLib.config =
  {code_eq = contract_code_eq, parsed_eq = parsed_contract_code_eq,
   hints = [],
   simps = extra @ [with_zero_def, mask_and_w2w, getter_memory_cost_64_32,
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

fun getter_compose_with extra path =
  let
    val ths = map (fn (n,v) => inline_memory (weth_block n v)) path
    val th0 = hd ths
    val th0 = INST [var_named th0 "m" |-> ``empty_buffer``,
                    var_named th0 "g" |-> ``0n``] th0
  in
    List.foldl (fn (th, acc) => compose_blocks (getter_config extra) [acc, th])
      th0 (tl ths)
  end

val getter_compose = getter_compose_with []

val getter_dispatch = [(0,"_skip"),(13,"_skip"),(65,"_skip")]
val totalSupply_path_composed = getter_compose
  (getter_dispatch @ [(76,"_take"),(417,"_take"),(428,"_Jump"),
                       (1645,"_Jump"),(436,"_outermost")])
val decimals_path_composed = getter_compose
  (getter_dispatch @ [(76,"_skip"),(87,"_skip"),(98,"_skip"),
    (109,"_take"),(614,"_take"),(625,"_Jump"),(2821,"_Jump"),
    (633,"_outermost")])

val balanceOf_path_composed = getter_compose
  (getter_dispatch @ [(76,"_skip"),(87,"_skip"),(98,"_skip"),
    (109,"_skip"),(120,"_take"),(661,"_take"),(672,"_Jump"),
    (2840,"_Jump"),(716,"_outermost")])
val allowance_path_composed = getter_compose
  (getter_dispatch @ [(76,"_skip"),(87,"_skip"),(98,"_skip"),
    (109,"_skip"),(120,"_skip"),(131,"_skip"),(142,"_skip"),
    (153,"_skip"),(164,"_take"),(980,"_take"),(991,"_Jump"),
    (3043,"_Jump"),(1066,"_outermost")])

fun getter_ground_div tm =
  let val (f,_) = strip_comb tm in
    if is_const f andalso
       Lib.mem (fst (dest_const f)) ["with_zero", "word_div"] andalso
       null (free_vars tm)
    then let val th = EVAL tm in
      if rhs (concl th) ~~ tm then raise UNCHANGED else th end
    else raise UNCHANGED
  end
val () = augment_srw_ss [simpLib.named_merge_ss "getter_ground_div"
  [simpLib.conv_ss {name = "getter_ground_div", trace = 3,
    key = SOME ([], mk_var ("x", alpha)),
    conv = K (K getter_ground_div)}]]

val symbol_slot = ASSUME ``lookup_storage 1w
  (lookup_account (p:message_parameters).callee (rb:rollback_state).accounts).storage =
  0x5745544800000000000000000000000000000000000000000000000000000008w``
val symbol_path_composed = getter_compose_with [symbol_slot]
  (getter_dispatch @ [(76,"_skip"),(87,"_skip"),(98,"_skip"),
    (109,"_skip"),(120,"_skip"),(131,"_take"),(738,"_take"),(749,"_Jump"),
    (2864,"_skip"),(2944,"_skip"),(2952,"_Jump"),(3014,"_Jump"),
    (757,""),(794,"_skip"),(803,"_Jump"),(794,"_take"),
    (821,"_skip"),(841,""),(866,"_outermost")])
val () = diminish_srw_ss ["getter_ground_div"]

val () = List.app (fn th => if null (hyp th) then () else
  raise mk_HOL_ERR "wrappedEtherGettersScript" "getter_compose" "hypotheses")
  [totalSupply_path_composed, decimals_path_composed, balanceOf_path_composed,
   allowance_path_composed, symbol_path_composed]

fun getter_spec_start th =
  let
    val e = var_named th "e"
  in
    INST [e |-> sumSyntax.mk_inl (``()``, snd (sumSyntax.dest_sum (type_of e))),
          var_named th "j" |-> optionSyntax.mk_none
            (optionSyntax.dest_option (type_of (var_named th "j"))),
          var_named th "cs" |-> listSyntax.mk_nil
            (listSyntax.dest_list_type (type_of (var_named th "cs"))),
          var_named th "rest" |-> listSyntax.mk_nil
            (listSyntax.dest_list_type (type_of (var_named th "rest"))),
          var_named th "codeCost" |-> ``0n``] th
  end

fun getter_ground_conv tm =
  if null (free_vars tm) andalso not (is_const tm) andalso
     not (numSyntax.is_numeral tm) andalso
     (type_of tm = numSyntax.num orelse
      type_of tm = ``:word8 list``)
  then let val th = cv_eval tm handle Interrupt => raise Interrupt | _ => EVAL tm in
    if rhs (concl th) ~~ tm then raise UNCHANGED else th end
  else raise UNCHANGED

fun getter_spec_eval th =
  CONV_RULE (TOP_SWEEP_CONV getter_ground_conv) (getter_spec_start th)
val totalSupply_spec_eval = getter_spec_eval totalSupply_path_composed
val decimals_spec_eval = getter_spec_eval decimals_path_composed
val balanceOf_spec_eval = getter_spec_eval balanceOf_path_composed
val allowance_spec_eval = getter_spec_eval allowance_path_composed
val symbol_spec_eval = getter_spec_eval symbol_path_composed
(* Restrict the boundary to ordinary calls, so Return cannot deposit code. *)
fun getter_call_spec th =
  let
    val not_create = ``~is_code_dest (p:message_parameters).outputTo``
  in
    DISCH not_create
      (SIMP_RULE (srw_ss()) [ASSUME not_create, word_exp_def,
                            word_div_1] th)
  end
val totalSupply_call_spec = getter_call_spec totalSupply_spec_eval
val decimals_call_spec = getter_call_spec decimals_spec_eval
val balanceOf_call_spec = getter_call_spec balanceOf_spec_eval
val allowance_call_spec = getter_call_spec allowance_spec_eval
val symbol_call_spec = getter_call_spec symbol_spec_eval
val getter_selector_reads = map (fn sel =>
  INST [``sel:word8 list`` |-> sel] getter_selector_calldata
  |> SIMP_RULE (srw_ss()) [num_of_bytes_def])
  [``[0x95w; 0xD8w; 0x9Bw; 0x41w] : word8 list``,
   ``[0x31w; 0x3Cw; 0xE5w; 0x67w] : word8 list``,
   ``[0x18w; 0x16w; 0x0Dw; 0xDDw] : word8 list``,
   ``[0x70w; 0xA0w; 0x82w; 0x31w] : word8 list``,
   ``[0xDDw; 0x62w; 0xEDw; 0x3Ew] : word8 list``]
val getter_slot_bytes = map (fn tm => GSYM (EVAL tm))
  [``word_to_bytes (3w:bytes32) T``, ``word_to_bytes (4w:bytes32) T``]

fun getter_calldata_spec data th =
  let
    val input = mk_eq (``buffer_to_list (p:message_parameters).data``, data)
    val th = UNDISCH th
    val th = SIMP_RULE (srw_ss())
      [ASSUME input, getter_selector_calldata, getter_selectors,
       getter_address_enc, DROP_APPEND, DROP_LENGTH_TOO_LONG, calldata_word,
       mask_and_w2w, REVERSE_word_to_bytes_bytes32] th
    val th = SIMP_RULE (srw_ss()) getter_selector_reads th
    val th = CONV_RULE (TOP_SWEEP_CONV getter_ground_conv) th
    val th = REWRITE_RULE (getter_slot_bytes @
      [GSYM word_of_bytes_be_def, getter_balance_key, getter_allowance_key]) th
    val th = SIMP_RULE (srw_ss())
      [Keccak256_gas_0_64, buffer_length_expanded_memory,
       word_to_bytes_bytes32_NIL, expanded_memory_leq, MAX_LE] th
  in DISCH_ALL th end
val totalSupply_input_spec = getter_calldata_spec
  ``function_selector "totalSupply" [] ++ tail`` totalSupply_call_spec
val decimals_input_spec = getter_calldata_spec
  ``function_selector "decimals" [] ++ tail`` decimals_call_spec
val symbol_input_spec = getter_calldata_spec
  ``function_selector "symbol" [] ++ tail`` symbol_call_spec
val balanceOf_input_spec = getter_calldata_spec
  ``function_selector "balanceOf" [Address] ++
    enc (Tuple [Address]) (ListV [NumV (w2n (a:address))]) ++ tail``
  balanceOf_call_spec
val allowance_input_spec = getter_calldata_spec
  ``function_selector "allowance" [Address; Address] ++
    enc (Tuple [Address; Address])
      (ListV [NumV (w2n (owner:address)); NumV (w2n (spender:address))]) ++ tail``
  allowance_call_spec
Theorem getter_numeric_output[local]:
  n < 2 ** 256 ==>
  word_to_bytes (n2w n : bytes32) T =
    enc (Tuple [Uint 256]) (ListV [NumV n])
Proof
  simp[head_lengths_def, REV_DEF]
QED

Theorem getter_address_roundtrip[local]:
  w2w (w2w (a:address) : bytes32) = (a:address)
Proof
  `w2n a < 2 ** 256` by
    (qspec_then `a` mp_tac w2n_lt >> simp[dimword_def])
  >> gvs[w2w_def, w2n_n2w, dimword_def]
QED

fun getter_result_spec facts th =
  UNDISCH_ALL th
  |> SIMP_RULE (srw_ss()) (facts @ [getter_warm_slot_gas, getter_address_roundtrip])
  |> DISCH_ALL

val symbol_result_spec = REWRITE_RULE
  [GSYM (cv_eval ``enc (Tuple [String])
     (ListV [BytesV (MAP (n2w o ORD) "WETH")])``)] symbol_input_spec

val decimals_result_spec =
  getter_result_spec
    [ASSUME ``lookup_storage 2w
       (lookup_account (p:message_parameters).callee (rb:rollback_state).accounts).storage = 18w``]
    decimals_input_spec
  |> CONV_RULE (TOP_SWEEP_CONV getter_ground_conv)
  |> REWRITE_RULE [GSYM (cv_eval ``enc (Tuple [Uint 8]) (ListV [NumV 18])``)]

val totalSupply_result_spec = getter_result_spec
  [ASSUME ``(lookup_account (p:message_parameters).callee
       (rb:rollback_state).accounts).balance = n``,
   ASSUME ``n < 2 ** 256``] totalSupply_input_spec
  |> PURE_REWRITE_RULE [UNDISCH getter_numeric_output]
  |> DISCH_ALL

val balanceOf_result_spec = getter_result_spec
  [ASSUME ``lookup_storage (balance_slot_key a)
       (lookup_account (p:message_parameters).callee (rb:rollback_state).accounts).storage = n2w n``,
   ASSUME ``n < 2 ** 256``]
  balanceOf_input_spec
  |> PURE_REWRITE_RULE [UNDISCH getter_numeric_output]
  |> DISCH_ALL

val allowance_result_spec = getter_result_spec
  [ASSUME ``lookup_storage (allowance_slot_key owner spender)
       (lookup_account (p:message_parameters).callee (rb:rollback_state).accounts).storage = n2w n``,
   ASSUME ``n < 2 ** 256``]
  allowance_input_spec
  |> PURE_REWRITE_RULE [UNDISCH getter_numeric_output]
  |> DISCH_ALL

(* These conditional summaries are the boundary used by transaction lifting.
   All assumptions are explicit antecedents; the return data is ABI encoded,
   and getter_path_gas_bounds validates every path at the 4000 call budget.
   Only access bookkeeping changes in the rollback state. *)
val () = List.app (fn th => if null (hyp th) then () else
  raise mk_HOL_ERR "wrappedEtherGettersScript" "getter_result_spec" "hypotheses")
  [totalSupply_result_spec, decimals_result_spec, balanceOf_result_spec,
   allowance_result_spec, symbol_result_spec]

Theorem transfer_value_zero[local]:
  transfer_value f t 0 = I
Proof
  simp[FUN_EQ_THM, transfer_value_def]
QED

Theorem getter_model_instr[local]:
  FST (SND (SND EVM_MODEL)) = EVM_INSTR
Proof
  simp[EVM_MODEL_def]
QED

fun getter_dest_star tm =
  case strip_comb tm of
    (f,[a,b]) =>
      if same_const f ``STAR`` then (f,a,b)
      else raise mk_HOL_ERR "wrappedEtherGettersScript" "dest_star" ""
  | _ => raise mk_HOL_ERR "wrappedEtherGettersScript" "dest_star" ""
fun getter_strip_star tm =
  let val (_,a,b) = getter_dest_star tm
  in getter_strip_star a @ getter_strip_star b end
  handle HOL_ERR _ => [tm]

(* Keep code inclusion as an explicit lifting premise; its finite check is
   performed in Theorem proofs, not by a programmatic proof constructor. *)
fun getter_lift spec =
  let
    val th = UNDISCH_ALL spec
    val th = MATCH_MP SPEC_SUBSET_CODE th
             |> Q.SPEC `fmap_entries parsed_contract_code` |> UNDISCH
    val th = Q.SPEC `evm_Logs logs * evm_AddRefund addRefund *
        evm_SubRefund subRefund * evm_TxParams txParams * SEP_T`
        (MATCH_MP SPEC_FRAME th)
      |> ONCE_REWRITE_RULE [GSYM SPEC_CODE]
      |> REWRITE_RULE [getter_model_instr]
    val post = rand (concl th)
    val (star,_,_) = getter_dest_star post
    fun mk_star (a,b) = list_mk_comb (star,[a,b])
    fun head_name tm = fst (dest_const (fst (strip_comb tm)))
    val factors = getter_strip_star post
    val names = ["evm_Exception", "evm_ReturnData", "evm_Logs",
      "evm_Rollback", "evm_Contexts", "evm_GasUsed", "evm_MsgParams",
      "evm_AddRefund", "evm_SubRefund", "evm_TxParams"]
    val picked = map (fn n => valOf (List.find (fn f => head_name f = n) factors)) names
    val others = List.filter (fn f => not (Lib.mem (head_name f) names)) factors
    val rest = List.foldl (fn (f,a) => mk_star (a,f)) (hd others) (tl others)
    val post' = List.foldl (fn (f,a) => mk_star (a,f)) (hd picked) (tl picked @ [rest])
    val th = CONV_RULE (RAND_CONV
      (SIMP_CONV bool_ss [AC STAR_ASSOC STAR_COMM])) th
    val ordered = EQT_ELIM (SIMP_CONV bool_ss [AC STAR_ASSOC STAR_COMM]
      (mk_eq (rand (concl th),post')))
    val th = CONV_RULE (RAND_CONV (REWR_CONV ordered)) th
    val th = MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] SPEC_to_run_transaction) th
    val (ants,_) = strip_imp (concl th)
    val (q,form) = dest_eq (last ants)
    val (tmS,tyS) = match_term form q
    val th = INST tmS (INST_TYPE tyS th) |> REWRITE_RULE [AND_IMP_INTRO]
    val th = INST [var_named th "s''" |-> ``s':execution_state``,
                   var_named th "s'''" |-> ``s:execution_state``] th
  in DISCH_ALL th end

val symbol_lift = getter_lift symbol_result_spec
val decimals_lift = getter_lift decimals_result_spec
val totalSupply_lift = getter_lift totalSupply_result_spec
fun getter_code_tac g =
  (rewrite_tac [SUBSET_DEF] >> Cases
   >> rewrite_tac [IN_INSERT, NOT_IN_EMPTY, PAIR_EQ]
   >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC
   >> simp [fmap_entries_def]
   >> CONV_TAC (REWRITE_CONV [parsed_contract_code_eq] THENC EVAL)) g

Theorem weth_symbol_run_transaction[local]:
  (lookup_account addr accounts).code = contract_code /\
  lookup_storage 1w (lookup_account addr accounts).storage =
    0x5745544800000000000000000000000000000000000000000000000000000008w /\
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "symbol" []) 4000 s /\
  access_slot_check dom (SK addr 1w)
  ==>
  ?result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') /\
    result.result = NONE /\
    result.output = enc (Tuple [String]) (ListV [BytesV (MAP (n2w o ORD) "WETH")]) /\
    result.logs = [] /\
    !b. (lookup_account b accounts').code =
          (lookup_account b s.rollback.accounts).code /\
        (lookup_account b accounts').storage =
          (lookup_account b s.rollback.accounts).storage /\
        (lookup_account b accounts').nonce =
          (lookup_account b s.rollback.accounts).nonce
Proof
  PURE_REWRITE_TAC [zero_value_call_def]
  >> strip_tac
  >> strip_assume_tac contract_code_not_delegation
  >> drule_all initial_state_call_code >> strip_tac
  >> fs[GSYM parsed_contract_code_def]
  >> drule_all wf_initial_state >> strip_tac
  >> `?tail. tx.data = function_selector "symbol" [] ++ tail`
     by gvs[IS_PREFIX_APPEND]
  >> mp_tac (Q.INST [`p` |-> `ctxt.msgParams`, `rb` |-> `s.rollback`,
       `d` |-> `dom`, `rd` |-> `[]`, `logs` |-> `[]`,
       `addRefund` |-> `0`, `subRefund` |-> `0`,
       `txParams` |-> `s.txParams`, `callee` |-> `addr`,
       `s'` |-> `s with rollback updated_by
          (\r. r with accounts updated_by transfer_value tx.from addr tx.value)`]
       symbol_lift)
  >> (impl_tac >- getter_code_tac)
  >> asm_rewrite_tac [buffer_to_list_of_list]
  >> impl_tac
  >- (simp_tac pure_ss [evm2set_def, GSYM STAR_ASSOC]
      >> simp[STAR_evm2set, STAR_CODE_POOL_evm2set, cond_STAR, SEP_T_def,
           transfer_value_zero, execution_state_component_equality,
           rollback_state_component_equality, fmap_entries_def]
      >> `s with rollback updated_by
           (\r. r with accounts updated_by I) = s` by
         simp[execution_state_component_equality, rollback_state_component_equality]
      >> `LENGTH tail + 4 <= 16777216` by gvs[getter_selectors]
      >> `LENGTH tail + 4 < 2 ** 256` by simp[]
      >> gvs[getter_selectors, getter_warm_slot_gas]
      >> rw[access_slot_cost_def, warm_access_cost_def, cold_sload_cost_def])
  >> strip_tac >> gvs[accesses_add_slot_def]
QED

Theorem weth_decimals_run_transaction[local]:
  (lookup_account addr accounts).code = contract_code /\
  lookup_storage 2w (lookup_account addr accounts).storage = 18w /\
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "decimals" []) 4000 s /\
  access_slot_check dom (SK addr 2w)
  ==>
  ?result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') /\
    result.result = NONE /\
    result.output = enc (Tuple [Uint 8]) (ListV [NumV 18]) /\
    result.logs = [] /\
    !b. (lookup_account b accounts').code =
          (lookup_account b s.rollback.accounts).code /\
        (lookup_account b accounts').storage =
          (lookup_account b s.rollback.accounts).storage /\
        (lookup_account b accounts').nonce =
          (lookup_account b s.rollback.accounts).nonce
Proof
  PURE_REWRITE_TAC [zero_value_call_def]
  >> strip_tac
  >> strip_assume_tac contract_code_not_delegation
  >> drule_all initial_state_call_code >> strip_tac
  >> fs[GSYM parsed_contract_code_def]
  >> drule_all wf_initial_state >> strip_tac
  >> `?tail. tx.data = function_selector "decimals" [] ++ tail`
     by gvs[IS_PREFIX_APPEND]
  >> mp_tac (Q.INST [`p` |-> `ctxt.msgParams`, `rb` |-> `s.rollback`,
       `d` |-> `dom`, `rd` |-> `[]`, `logs` |-> `[]`,
       `addRefund` |-> `0`, `subRefund` |-> `0`,
       `txParams` |-> `s.txParams`, `callee` |-> `addr`,
       `s'` |-> `s with rollback updated_by
          (\r. r with accounts updated_by transfer_value tx.from addr tx.value)`]
       decimals_lift)
  >> (impl_tac >- getter_code_tac)
  >> asm_rewrite_tac [buffer_to_list_of_list]
  >> (impl_tac >- gvs[getter_selectors])
  >> impl_tac
  >- (simp_tac pure_ss [evm2set_def, GSYM STAR_ASSOC]
      >> simp[STAR_evm2set, STAR_CODE_POOL_evm2set, cond_STAR, SEP_T_def,
           transfer_value_zero, execution_state_component_equality,
           rollback_state_component_equality, fmap_entries_def]
      >> `s with rollback updated_by
           (\r. r with accounts updated_by I) = s` by
         simp[execution_state_component_equality, rollback_state_component_equality]
      >> `LENGTH tail + 4 <= 16777216` by gvs[getter_selectors]
      >> `LENGTH tail + 4 < 2 ** 256` by simp[]
      >> gvs[getter_selectors]
      >> rw[access_slot_cost_def, warm_access_cost_def, cold_sload_cost_def])
  >> strip_tac >> gvs[accesses_add_slot_def]
QED

Theorem WETH_EVM_symbol_run_transaction:
  WETH_EVM addr ws accounts ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "symbol" []) 4000 s ∧
  access_slot_check dom (SK addr 1w)
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = enc (Tuple [String]) (ListV [BytesV (MAP (n2w o ORD) "WETH")]) ∧
    result.logs = [] ∧
    ∀b. (lookup_account b accounts').code =
          (lookup_account b s.rollback.accounts).code ∧
        (lookup_account b accounts').storage =
          (lookup_account b s.rollback.accounts).storage ∧
        (lookup_account b accounts').nonce =
          (lookup_account b s.rollback.accounts).nonce
Proof
  strip_tac >> irule weth_symbol_run_transaction
  >> qexists_tac `addr` >> gvs[WETH_EVM_def, LET_THM]
QED

Theorem WETH_EVM_decimals_run_transaction:
  WETH_EVM addr ws accounts ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "decimals" []) 4000 s ∧
  access_slot_check dom (SK addr 2w)
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = enc (Tuple [Uint 8]) (ListV [NumV 18]) ∧
    result.logs = [] ∧
    ∀b. (lookup_account b accounts').code =
          (lookup_account b s.rollback.accounts).code ∧
        (lookup_account b accounts').storage =
          (lookup_account b s.rollback.accounts).storage ∧
        (lookup_account b accounts').nonce =
          (lookup_account b s.rollback.accounts).nonce
Proof
  strip_tac >> irule weth_decimals_run_transaction
  >> qexists_tac `addr` >> gvs[WETH_EVM_def, LET_THM]
QED

Theorem WETH_EVM_totalSupply_run_transaction:
  WETH_EVM addr ws accounts ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "totalSupply" []) 4000 s ∧
  access_check dom addr
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = enc (Tuple [Uint 256]) (ListV [NumV ws.locked]) ∧
    result.logs = [] ∧
    ∀b. (lookup_account b accounts').code =
          (lookup_account b s.rollback.accounts).code ∧
        (lookup_account b accounts').storage =
          (lookup_account b s.rollback.accounts).storage ∧
        (lookup_account b accounts').nonce =
          (lookup_account b s.rollback.accounts).nonce
Proof
  strip_tac
  >> drule_all getter_call_balance >> strip_tac
  >> drule getter_bounds >> strip_tac
  >> `(lookup_account addr accounts).code = contract_code`
     by gvs[WETH_EVM_def, LET_THM]
  >> qpat_x_assum `WETH_EVM _ _ _` kall_tac
  >> qpat_x_assum `!a. ws.balances a < _` kall_tac
  >> qpat_x_assum `!owner spender. ws.allowances owner spender < _` kall_tac
  >> fs[zero_value_call_def]
  >> strip_assume_tac contract_code_not_delegation
  >> drule_all initial_state_call_code >> strip_tac
  >> fs[GSYM parsed_contract_code_def]
  >> drule_all wf_initial_state >> strip_tac
  >> `?tail. tx.data = function_selector "totalSupply" [] ++ tail`
     by gvs[IS_PREFIX_APPEND]
  >> mp_tac (Q.INST [`p` |-> `ctxt.msgParams`, `rb` |-> `s.rollback`,
       `d` |-> `dom`, `rd` |-> `[]`, `logs` |-> `[]`,
       `addRefund` |-> `0`, `subRefund` |-> `0`, `n` |-> `ws.locked`,
       `txParams` |-> `s.txParams`, `callee` |-> `addr`,
       `s'` |-> `s with rollback updated_by
          (\r. r with accounts updated_by transfer_value tx.from addr tx.value)`]
       totalSupply_lift)
  >> (impl_tac >- getter_code_tac)
  >> asm_rewrite_tac [buffer_to_list_of_list]
  >> (impl_tac >- simp[])
  >> impl_tac
  >- (simp_tac pure_ss [evm2set_def, GSYM STAR_ASSOC]
      >> simp[STAR_evm2set, STAR_CODE_POOL_evm2set, cond_STAR, SEP_T_def,
           transfer_value_zero, execution_state_component_equality,
           rollback_state_component_equality, fmap_entries_def]
      >> `s with rollback updated_by
           (\r. r with accounts updated_by I) = s` by
         simp[execution_state_component_equality, rollback_state_component_equality]
      >> `LENGTH tail + 4 <= 16777216` by gvs[getter_selectors]
      >> `LENGTH tail + 4 < 2 ** 256` by simp[]
      >> gvs[getter_selectors]
      >> rw[Balance_gas_def, access_cost_def, warm_access_cost_def,
            cold_access_cost_def, vfmOperationTheory.static_gas_def])
  >> strip_tac >> gvs[accesses_add_def]
QED

Theorem WETH_EVM_balanceOf_run_transaction:
  WETH_EVM addr ws accounts ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "balanceOf" [Address] ++
     enc (Tuple [Address]) (ListV [NumV (w2n a)])) 4000 s ∧
  balance_slot_key a ∉ {0w; 1w; 2w} ∧
  (a ∈ ws.touched ∨
   balance_slot_key a ∉ IMAGE balance_slot_key ws.touched) ∧
  access_slot_check dom (SK addr (balance_slot_key a))
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = enc (Tuple [Uint 256]) (ListV [NumV (ws.balances a)]) ∧
    result.logs = [] ∧
    ∀b. (lookup_account b accounts').code =
          (lookup_account b s.rollback.accounts).code ∧
        (lookup_account b accounts').storage =
          (lookup_account b s.rollback.accounts).storage ∧
        (lookup_account b accounts').nonce =
          (lookup_account b s.rollback.accounts).nonce
Proof
  cheat
QED

Theorem WETH_EVM_allowance_run_transaction:
  WETH_EVM addr ws accounts ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "allowance" [Address; Address] ++
     enc (Tuple [Address; Address])
       (ListV [NumV (w2n owner); NumV (w2n spender)])) 4000 s ∧
  allowance_slot_key owner spender ∉ {0w; 1w; 2w} ∧
  allowance_slot_key owner spender ∉ IMAGE balance_slot_key ws.touched ∧
  ((owner, spender) ∈ ws.allowances_touched ∨
   allowance_slot_key owner spender ∉
     IMAGE (λ(owner, spender). allowance_slot_key owner spender)
       ws.allowances_touched) ∧
  access_slot_check dom (SK addr (allowance_slot_key owner spender))
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = enc (Tuple [Uint 256]) (ListV [NumV (ws.allowances owner spender)]) ∧
    result.logs = [] ∧
    ∀b. (lookup_account b accounts').code =
          (lookup_account b s.rollback.accounts).code ∧
        (lookup_account b accounts').storage =
          (lookup_account b s.rollback.accounts).storage ∧
        (lookup_account b accounts').nonce =
          (lookup_account b s.rollback.accounts).nonce
Proof
  cheat
QED

