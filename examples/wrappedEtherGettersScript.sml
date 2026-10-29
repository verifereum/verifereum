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
  cheat
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
  cheat
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
  cheat
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

