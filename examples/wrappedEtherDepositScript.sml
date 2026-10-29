(* WETH's deposit() and fallback, from the block summaries of
   wrappedEtherTheory composed along their paths and lifted to
   run_transaction. *)
Theory wrappedEtherDeposit
Ancestors
  arithmetic list rich_list combin pair pred_set byte cv_std words
  vfmTypes vfmConstants vfmState vfmContext vfmExecution vfmExecutionProp
  vfmBuffer
  set_sep prog vfmProg contractABI wrappedEther wrappedEtherName
  wrappedEtherTransfer
Libs
  dep_rewrite wordsLib cv_transLib evmDecompLib wrappedEtherPathLib

(* ---------------------------------------------------------------- *)
(* Paying value into a contract *)

Theorem lookup_account_transfer_value_fields:
  (lookup_account a (transfer_value x y v accs)).code =
    (lookup_account a accs).code ∧
  (lookup_account a (transfer_value x y v accs)).storage =
    (lookup_account a accs).storage ∧
  (lookup_account a (transfer_value x y v accs)).nonce =
    (lookup_account a accs).nonce
Proof
  rw[transfer_value_def, lookup_account_def, update_account_def,
     APPLY_UPDATE_THM]
  \\ rw[COND_RAND]
QED

Theorem lookup_account_transfer_value_to:
  x ≠ y ⇒
  lookup_account y (transfer_value x y v accs) =
  lookup_account y accs with balance := (lookup_account y accs).balance + v
Proof
  rw[transfer_value_def, lookup_account_def, update_account_def,
     APPLY_UPDATE_THM, account_state_component_equality]
QED

(* the same with lookup_account unfolded *)
Theorem transfer_value_fields[local]:
  (transfer_value x y v accs a).code = (accs a).code ∧
  (transfer_value x y v accs a).storage = (accs a).storage ∧
  (transfer_value x y v accs a).nonce = (accs a).nonce
Proof
  metis_tac[lookup_account_transfer_value_fields, lookup_account_def]
QED

Theorem transfer_value_to[local]:
  x ≠ y ⇒
  transfer_value x y v accs y = accs y with balance := (accs y).balance + v
Proof
  metis_tac[lookup_account_transfer_value_to, lookup_account_def]
QED

(* ---------------------------------------------------------------- *)
(* Calldata *)

Theorem deposit_selector_eq:
  function_selector "deposit" [] = [0xD0w; 0xE3w; 0x0Dw; 0xB0w]
Proof
  CONV_TAC (LAND_CONV cv_eval) \\ rw[]
QED

Theorem deposit_selector_calldata:
  0xFFFFFFFFw &&
  word_of_bytes F 0w
    (REVERSE (take_pad_0 32 ([0xD0w; 0xE3w; 0x0Dw; 0xB0w] ++ rest))) //
  (0x100000000000000000000000000000000000000000000000000000000w : bytes32)
  = 0xD0E30DB0w
Proof
  qabbrev_tac `sel = [0xD0w; 0xE3w; 0x0Dw; 0xB0w] : word8 list`
  \\ `∃r. take_pad_0 32 (sel ++ rest) = sel ++ r ∧ LENGTH r = 28`
  by rw[take_pad_0_def, TAKE_APPEND, PAD_RIGHT, Abbr`sel`, LENGTH_TAKE_EQ]
  \\ simp[GSYM word_of_bytes_le_def]
  \\ DEP_REWRITE_TAC[word_of_bytes_le_eq_num_of_bytes]
  \\ simp[REVERSE_APPEND, num_of_bytes_APPEND, word_div_def]
  \\ qspec_then `REVERSE r` assume_tac num_of_bytes_lt
  \\ `num_of_bytes (REVERSE sel) = 0xD0E30DB0`
  by simp[Abbr`sel`, num_of_bytes_def, dimword_8]
  \\ gvs[]
  \\ `num_of_bytes (REVERSE r) + 256 ** 28 * 0xD0E30DB0 < dimword (:256)`
  by simp[]
  \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ qmatch_goalsub_abbrev_tac `(a + b) DIV c`
  \\ `a < c` by simp[Abbr`a`, Abbr`c`]
  \\ `(a + b) DIV c = 3504541104`
  by (`a + b = 3504541104 * c + a` by simp[Abbr`b`, Abbr`c`]
      \\ pop_assum SUBST1_TAC
      \\ simp[ADD_DIV_ADD_DIV, LESS_DIV_EQ_ZERO, Abbr`c`])
  \\ simp[]
QED

(* ---------------------------------------------------------------- *)
(* The paths, composed from the block summaries and lifted *)

(* the selector chain to deposit() at 153, its entry at 970 calling the
   deposit code at 1088, which returns to the STOP at 978 *)
val deposit_path =
  [(0, "_skip"), (13, "_skip"), (65, "_skip"), (76, "_skip"), (87, "_skip"),
   (98, "_skip"), (109, "_skip"), (120, "_skip"), (131, "_skip"),
   (142, "_skip"), (153, "_take"), (970, "_Jump"), (1088, "_Jump"),
   (978, "_outermost")]

(* calldata under 4 bytes: 0 jumps to 175, which calls the deposit code at
   1088, which returns to the STOP at 183 *)
val fallback_path =
  [(0, "_take"), (175, "_Jump"), (1088, "_Jump"), (183, "_outermost")]

fun success_lift path =
  path |> compose_path |> path_reads |> path_keys |> spec_start
  |> spec_code |> spec_pool
  |> spec_ordered ["evm_Exception", "evm_ReturnData", "evm_Logs",
                   "evm_Rollback", "evm_Contexts", "evm_GasUsed",
                   "evm_MsgParams", "evm_AddRefund", "evm_SubRefund",
                   "evm_TxParams"]
  |> spec_lift SPEC_to_run_transaction

val deposit_lift = success_lift deposit_path
val fallback_lift = success_lift fallback_path


Theorem transfer_value_enc[local]:
  enc (Tuple [Uint 256]) (ListV [NumV wad]) = word_to_bytes (n2w wad : bytes32) T
Proof
  simp[head_lengths_def, REV_DEF]
QED

(* the lift's hypotheses at a call's initial state s, after the value is
   paid in; the call data facts are given by calldata *)
fun deposit_tac lift calldata =
  PURE_REWRITE_TAC [cv_eval “word_of_bytes_be (Keccak_256_string
                       "Deposit(address,uint256)") : bytes32”,
                    transfer_value_enc, contract_call_def]
  \\ strip_tac
  \\ strip_assume_tac contract_code_not_delegation
  \\ drule_all initial_state_call_code \\ strip_tac
  \\ drule initial_state_contract
  \\ disch_then (qspec_then `addr` mp_tac)
  \\ impl_tac >- gvs[]
  \\ strip_tac
  \\ fs[GSYM parsed_contract_code_def]
  \\ drule_all wf_initial_state \\ strip_tac
  \\ calldata
  \\ `tx.from ≠ addr` by gvs[]
  \\ mp_tac (Q.INST [‘p’ |-> ‘ctxt.msgParams’,
                     ‘rb’ |-> ‘s.rollback with accounts updated_by
                                 transfer_value tx.from addr tx.value’,
                     ‘d’ |-> ‘dom’, ‘rd’ |-> ‘[]’, ‘l’ |-> ‘[]’,
                     ‘ar’ |-> ‘0’, ‘sr’ |-> ‘0’,
                     ‘original’ |-> ‘s.originalAccounts’,
                     ‘txParams’ |-> ‘s.txParams’, ‘callee’ |-> ‘addr’,
                     ‘s' : execution_state’ |-> ‘s : execution_state’,
                     ‘s’ |-> ‘s with rollback updated_by
                       (λr. r with accounts updated_by
                              transfer_value tx.from addr tx.value)’]
                    lift)
  \\ impl_tac
  >- (
    simp_tac pure_ss [evm2set_def, GSYM STAR_ASSOC]
    \\ simp[STAR_evm2set, STAR_evm_OriginalAccounts, STAR_CODE_POOL_evm2set,
            cond_STAR, SEP_T_def,
            execution_state_component_equality,
            rollback_state_component_equality, fmap_entries_def,
            SIMP_RULE std_ss [APPEND] deposit_selector_calldata,
            lookup_account_transfer_value_fields,
            lookup_account_transfer_value_to,
            balance_slot_key_bytes]
    \\ simp[access_slot_cost_add_slot, SStore_gas_add_slot,
            accesses_add_slot_accounts, lookup_account_transfer_value_fields]
    \\ qpat_assum `s.originalAccounts = _` (fn th => rewrite_tac[th])
    \\ qpat_assum `lookup_account addr s.rollback.accounts = _`
         (fn th => rewrite_tac[th])
    \\ gas_bounds_tac
    \\ gvs[call_stipend_def, wf_state_def, all_accounts_def,
           stack_room_ok_def, gas_stack_ok_def,
           outputTo_consistent_stack_def])
  \\ strip_tac
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ qpat_assum `∀a. lookup_account a accounts' = _`
       (qspec_then `addr` assume_tac)
  \\ gvs[lookup_account_transfer_value_fields,
         lookup_account_transfer_value_to]
  \\ Cases_on `ctxt.msgParams.outputTo` \\ gvs[is_code_dest_def]
  \\ CONV_TAC (QCONV (with_ground_div reads_conv))
  \\ PURE_REWRITE_TAC [balance_slot_key_bytes]
  \\ gvs[transfer_value_fields, transfer_value_to, SStore_write_def,
         sstore_write_accounts_updater_def, accesses_add_slot_def,
         lookup_account_def, update_account_def, APPLY_UPDATE_THM,
         balance_slot_key_bytes]
  \\ simp[REVERSE_word_to_bytes_bytes32]
  \\ simp[account_state_component_equality]
  \\ rw[FUN_EQ_THM]

(* deposit() pays tx.value into the caller's balance slot and logs it *)
Theorem weth_deposit_run_transaction:
  (lookup_account addr accounts).code = contract_code ∧
  contract_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "deposit" []) 23974 s ∧
  access_slot_check dom (SK addr (balance_slot_key tx.from)) ∧
  blk.coinBase ≠ addr
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = [] ∧
    result.logs =
      [<| logger := addr;
          topics :=
            [word_of_bytes_be
               (Keccak_256_string "Deposit(address,uint256)");
             w2w tx.from];
          data := enc (Tuple [Uint 256]) (ListV [NumV tx.value]) |>] ∧
    (∀a. a ≠ addr ⇒
         (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    lookup_account addr accounts' =
      let acc = lookup_account addr accounts;
          ks = balance_slot_key tx.from
      in acc with <| balance := acc.balance + tx.value;
                     storage := update_storage ks
                       (n2w tx.value + lookup_storage ks acc.storage)
                       acc.storage |>
Proof
  deposit_tac deposit_lift
    (`∃rest. tx.data = [0xD0w; 0xE3w; 0x0Dw; 0xB0w] ++ rest`
     by (qpat_x_assum `_ ≼ tx.data` mp_tac
         \\ rewrite_tac[deposit_selector_eq, IS_PREFIX_APPEND]))
QED

(* with calldata under 4 bytes, the fallback does the same *)
Theorem weth_fallback_run_transaction:
  (lookup_account addr accounts).code = contract_code ∧
  contract_call (dom, chainId, prevHashes, blk) accounts tx addr [] 23974 s ∧
  LENGTH tx.data < 4 ∧
  access_slot_check dom (SK addr (balance_slot_key tx.from)) ∧
  blk.coinBase ≠ addr
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = [] ∧
    result.logs =
      [<| logger := addr;
          topics :=
            [word_of_bytes_be
               (Keccak_256_string "Deposit(address,uint256)");
             w2w tx.from];
          data := enc (Tuple [Uint 256]) (ListV [NumV tx.value]) |>] ∧
    (∀a. a ≠ addr ⇒
         (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    lookup_account addr accounts' =
      let acc = lookup_account addr accounts;
          ks = balance_slot_key tx.from
      in acc with <| balance := acc.balance + tx.value;
                     storage := update_storage ks
                       (n2w tx.value + lookup_storage ks acc.storage)
                       acc.storage |>
Proof
  deposit_tac fallback_lift ALL_TAC
QED

(* ---------------------------------------------------------------- *)
(* The same over the WETH_EVM relation *)

Theorem lookup_update_storage[local]:
  lookup_storage k (update_storage k' v s) =
  if k' = k then v else lookup_storage k s
Proof
  rw[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
QED

(* the storage write of a deposit keeps the WETH_EVM relation *)
Theorem WETH_deposit_storage[local]:
  wf_WETH_state ws ∧ ws.locked + n < 2 ** 256 ∧
  (∀a. balance_slot_key a ∉ {0w; 1w; 2w} ∧
       (a ∈ ws.touched ∨ balance_slot_key a ∉ IMAGE balance_slot_key ws.touched) ⇒
       lookup_storage (balance_slot_key a) st = n2w (ws.balances a)) ∧
  (∀b. b ∈ ws.touched ∧ balance_slot_key b = balance_slot_key src ⇒ b = src) ∧
  balance_slot_key src ∉ {0w; 1w; 2w}
  ⇒
  let st' = update_storage (balance_slot_key src)
              (n2w n + lookup_storage (balance_slot_key src) st) st;
      ws' = WETH_deposit src n ws in
  wf_WETH_state ws' ∧
  (∀a. balance_slot_key a ∉ {0w; 1w; 2w} ∧
       (a ∈ ws'.touched ∨
        balance_slot_key a ∉ IMAGE balance_slot_key ws'.touched) ⇒
       lookup_storage (balance_slot_key a) st' = n2w (ws'.balances a)) ∧
  lookup_storage 0w st' = lookup_storage 0w st ∧
  lookup_storage 1w st' = lookup_storage 1w st ∧
  lookup_storage 2w st' = lookup_storage 2w st
Proof
  strip_tac
  \\ `lookup_storage (balance_slot_key src) st = n2w (ws.balances src)`
     by (first_assum irule \\ simp[] \\ metis_tac[])
  \\ simp_tac std_ss [LET_THM]
  \\ conj_tac >- (irule wf_WETH_deposit \\ asm_rewrite_tac[])
  \\ rpt (qpat_x_assum `balance_slot_key _ ∉ _`
            (strip_assume_tac o
             REWRITE_RULE [IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM]))
  \\ asm_rewrite_tac[lookup_update_storage]
  \\ simp[WETH_deposit_def]
  \\ gen_tac
  \\ Cases_on `a = src` >- simp[APPLY_UPDATE_THM, word_add_n2w]
  \\ strip_tac
  \\ `balance_slot_key src ≠ balance_slot_key a`
     by metis_tac[IN_IMAGE, IN_INSERT]
  \\ asm_simp_tac std_ss [APPLY_UPDATE_THM]
  \\ first_assum irule
  \\ asm_rewrite_tac[IN_INSERT, NOT_IN_EMPTY]
  \\ metis_tac[IN_IMAGE, IN_INSERT]
QED

(* deposit() over the WETH_EVM relation: the caller's balance and the
   locked ether grow by tx.value, assuming the caller's balance slot doesn't
   collide with a touched account's or with slots 0-2 *)
Theorem WETH_EVM_deposit_run_transaction:
  WETH_EVM addr ws accounts ∧
  contract_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "deposit" []) 23974 s ∧
  ws.locked + tx.value < 2 ** 256 ∧
  (∀b. b ∈ ws.touched ∧ balance_slot_key b = balance_slot_key tx.from ⇒
       b = tx.from) ∧
  balance_slot_key tx.from ∉ {0w; 1w; 2w} ∧
  access_slot_check dom (SK addr (balance_slot_key tx.from)) ∧
  blk.coinBase ≠ addr
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = [] ∧
    result.logs =
      [<| logger := addr;
          topics :=
            [word_of_bytes_be
               (Keccak_256_string "Deposit(address,uint256)");
             w2w tx.from];
          data := enc (Tuple [Uint 256]) (ListV [NumV tx.value]) |>] ∧
    (∀a. a ≠ addr ⇒
         (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    WETH_EVM addr (WETH_deposit tx.from tx.value ws) accounts'
Proof
  strip_tac
  \\ qpat_x_assum `WETH_EVM _ _ _`
       (strip_assume_tac o SIMP_RULE std_ss [WETH_EVM_def, LET_THM])
  \\ drule_at_then Any (drule_all_then strip_assume_tac)
       weth_deposit_run_transaction
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ asm_rewrite_tac[WETH_EVM_def]
  \\ qpat_x_assum `lookup_account addr accounts' = _` SUBST1_TAC
  \\ simp_tac std_ss [LET_THM]
  \\ mp_tac (Q.INST [`src` |-> `(tx:transaction).from`, `n` |-> `(tx:transaction).value`,
                     `st` |-> `(lookup_account addr accounts).storage`]
                    WETH_deposit_storage)
  \\ impl_tac >- asm_rewrite_tac[]
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ asm_rewrite_tac[account_state_accfupds, K_THM]
  \\ simp[WETH_deposit_def]
QED

(* the fallback over the WETH_EVM relation *)
Theorem WETH_EVM_fallback_run_transaction:
  WETH_EVM addr ws accounts ∧
  contract_call (dom, chainId, prevHashes, blk) accounts tx addr [] 23974 s ∧
  LENGTH tx.data < 4 ∧
  ws.locked + tx.value < 2 ** 256 ∧
  (∀b. b ∈ ws.touched ∧ balance_slot_key b = balance_slot_key tx.from ⇒
       b = tx.from) ∧
  balance_slot_key tx.from ∉ {0w; 1w; 2w} ∧
  access_slot_check dom (SK addr (balance_slot_key tx.from)) ∧
  blk.coinBase ≠ addr
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = NONE ∧
    result.output = [] ∧
    result.logs =
      [<| logger := addr;
          topics :=
            [word_of_bytes_be
               (Keccak_256_string "Deposit(address,uint256)");
             w2w tx.from];
          data := enc (Tuple [Uint 256]) (ListV [NumV tx.value]) |>] ∧
    (∀a. a ≠ addr ⇒
         (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    WETH_EVM addr (WETH_deposit tx.from tx.value ws) accounts'
Proof
  strip_tac
  \\ qpat_x_assum `WETH_EVM _ _ _`
       (strip_assume_tac o SIMP_RULE std_ss [WETH_EVM_def, LET_THM])
  \\ drule_at_then Any (drule_all_then strip_assume_tac)
       weth_fallback_run_transaction
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ asm_rewrite_tac[WETH_EVM_def]
  \\ qpat_x_assum `lookup_account addr accounts' = _` SUBST1_TAC
  \\ simp_tac std_ss [LET_THM]
  \\ mp_tac (Q.INST [`src` |-> `(tx:transaction).from`, `n` |-> `(tx:transaction).value`,
                     `st` |-> `(lookup_account addr accounts).storage`]
                    WETH_deposit_storage)
  \\ impl_tac >- asm_rewrite_tac[]
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ asm_rewrite_tac[account_state_accfupds, K_THM]
  \\ simp[WETH_deposit_def]
QED
