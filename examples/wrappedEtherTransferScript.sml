(* WETH's transfer(dst,wad), from the block summaries of wrappedEtherTheory
   composed along its path and lifted to run_transaction. *)
Theory wrappedEtherTransfer
Ancestors
  arithmetic list rich_list combin pair pred_set byte cv_std words
  vfmTypes vfmConstants vfmState vfmContext vfmExecution vfmExecutionProp
  vfmBuffer
  set_sep prog vfmProg contractABI wrappedEther wrappedEtherName
Libs
  dep_rewrite wordsLib cv_transLib evmDecompLib wrappedEtherPathLib

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
      ws'.allowances_touched = ws.allowances_touched ∧
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

Theorem transfer_value_enc[local]:
  enc (Tuple [Uint 256]) (ListV [NumV wad]) = word_to_bytes (n2w wad : bytes32) T
Proof
  simp[head_lengths_def, REV_DEF]
QED

(* ---------------------------------------------------------------- *)
(* The transfer path, composed from the block summaries and lifted *)

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

(* the same to the balance check at 1676, which fails, falling through to
   the REVERT at 1752 *)
val revert_path =
  List.take (transfer_path, 13) @ [(1676, "_skip"), (1752, "_outermost")]

val transfer_lift =
  transfer_path |> compose_path |> path_reads |> path_keys |> spec_start
  |> spec_code |> spec_pool
  |> spec_ordered ["evm_Exception", "evm_ReturnData", "evm_Logs",
                   "evm_Rollback", "evm_Contexts", "evm_GasUsed",
                   "evm_MsgParams", "evm_AddRefund", "evm_SubRefund",
                   "evm_TxParams"]
  |> spec_lift SPEC_to_run_transaction

val revert_lift =
  revert_path |> compose_path |> path_reads |> path_keys |> spec_start
  |> spec_code |> spec_pool
  |> spec_ordered ["evm_Exception", "evm_ReturnData", "evm_Contexts",
                   "evm_GasUsed", "evm_MsgParams", "evm_TxParams"]
  |> spec_lift SPEC_to_run_transaction_failure

Theorem weth_transfer_run_transaction:
  (lookup_account addr accounts).code = contract_code ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "transfer" [Address; Uint 256] ++
     enc (Tuple [Address; Uint 256]) (ListV [NumV (w2n dst); NumV wad]))
    29962 s ∧
  wad ≤ w2n (lookup_storage (balance_slot_key tx.from)
               (lookup_account addr accounts).storage) ∧
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
            SIMP_RULE std_ss [APPEND] transfer_selector_calldata,
            DROP_APPEND, DROP_LENGTH_TOO_LONG, calldata_word, mask_and_w2w,
            balance_slot_key_bytes]
    \\ simp[access_slot_cost_add_slot, SStore_gas_add_slot,
            accesses_add_slot_accounts]
    \\ qpat_assum `s.originalAccounts = _` (fn th => rewrite_tac[th])
    \\ qpat_assum `lookup_account addr s.rollback.accounts = _`
         (fn th => rewrite_tac[th])
    \\ qmatch_goalsub_abbrev_tac `sstore_base_gas c0 c0 v0`
    \\ `sstore_base_gas c0 c0 v0 ≤ 2900`
    by (irule sstore_base_gas_same_le \\ qunabbrevl_tac [`c0`, `v0`]
        \\ strip_tac \\ gvs[])
    \\ gas_bounds_tac
    \\ gvs[call_stipend_def])
  \\ strip_tac
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ qpat_assum `∀a. lookup_account a accounts' = _`
       (qspec_then `addr` assume_tac)
  \\ gvs[SStore_write_def, sstore_write_accounts_updater_def,
         accesses_add_slot_def, lookup_account_def, update_account_def,
         APPLY_UPDATE_THM, calldata_word, mask_and_w2w,
         DROP_APPEND, DROP_LENGTH_TOO_LONG, balance_slot_key_bytes]
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

Theorem WETH_transfer_allowance_storage[local]:
  wf_WETH_state ws ∧ wad ≤ ws.balances src ∧
  lookup_storage (balance_slot_key src) st = n2w (ws.balances src) ∧
  (∀owner spender.
     allowance_slot_key owner spender ∉ {0w; 1w; 2w} ∧
     allowance_slot_key owner spender ∉ IMAGE balance_slot_key ws.touched ∧
     ((owner, spender) ∈ ws.allowances_touched ∨
      allowance_slot_key owner spender ∉
        IMAGE (λ(owner, spender). allowance_slot_key owner spender)
          ws.allowances_touched) ⇒
     lookup_storage (allowance_slot_key owner spender) st =
       n2w (ws.allowances owner spender)) ⇒
  ∀owner spender.
     allowance_slot_key owner spender ∉ {0w; 1w; 2w} ∧
     allowance_slot_key owner spender ∉
       IMAGE balance_slot_key (WETH_transfer src dst wad ws).touched ∧
     ((owner, spender) ∈ (WETH_transfer src dst wad ws).allowances_touched ∨
      allowance_slot_key owner spender ∉
        IMAGE (λ(owner, spender). allowance_slot_key owner spender)
          (WETH_transfer src dst wad ws).allowances_touched) ⇒
     lookup_storage (allowance_slot_key owner spender)
       (update_storage (balance_slot_key dst)
         (lookup_storage (balance_slot_key dst)
           (update_storage (balance_slot_key src)
             (n2w (ws.balances src - wad)) st) + n2w wad)
         (update_storage (balance_slot_key src)
           (n2w (ws.balances src - wad)) st)) =
       n2w ((WETH_transfer src dst wad ws).allowances owner spender)
Proof
  simp_tac std_ss [LET_THM, WETH_transfer_def, WETH_state_accfupds,
                   WETH_state_accessors, IMAGE_INSERT, IN_INSERT]
  >> strip_tac >> rpt gen_tac
  >> disch_then (map_every assume_tac o CONJUNCTS)
  >> `lookup_storage (allowance_slot_key owner spender) st =
        n2w (ws.allowances owner spender)` by metis_tac[]
  >> Cases_on `balance_slot_key src = allowance_slot_key owner spender`
  >- (`src ∉ ws.touched` by metis_tac[IN_IMAGE]
      >> `ws.balances src = 0`
         by (gvs[wf_WETH_state_def, SUBSET_DEF]
             >> metis_tac[NOT_ZERO_LT_ZERO])
      >> `wad = 0` by decide_tac
      >> gvs[lookup_update_storage])
  >> simp[lookup_update_storage]
QED

(* the same from the WETH_EVM relation: the abstract state moves wad from
   the caller to dst, assuming the two balance slots involved don't collide
   with each other, with any touched account's slot, or with slots 0-2 *)
Theorem WETH_EVM_transfer_run_transaction:
  WETH_EVM addr ws accounts ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "transfer" [Address; Uint 256] ++
     enc (Tuple [Address; Uint 256]) (ListV [NumV (w2n dst); NumV wad]))
    29962 s ∧
  wad ≤ ws.balances tx.from ∧
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
  \\ mp_tac (Q.INST [`src` |-> `tx.from`, `dst` |-> `dst`,
                     `st` |-> `(lookup_account addr accounts).storage`]
                    WETH_transfer_allowance_storage)
  \\ (impl_tac >- asm_rewrite_tac[])
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ mp_tac (Q.INST [`src` |-> `tx.from`,
                     `st` |-> `(lookup_account addr accounts).storage`]
                    WETH_transfer_storage)
  \\ impl_tac >- asm_rewrite_tac[]
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ asm_rewrite_tac[account_state_accfupds, K_THM, WETH_transfer_locked]
QED

(* ---------------------------------------------------------------- *)
(* transfer reverts when the caller's balance is below wad *)

Theorem weth_transfer_revert_run_transaction:
  (lookup_account addr accounts).code = contract_code ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "transfer" [Address; Uint 256] ++
     enc (Tuple [Address; Uint 256]) (ListV [NumV (w2n dst); NumV wad]))
    2615 s ∧
  w2n (lookup_storage (balance_slot_key tx.from)
         (lookup_account addr accounts).storage) < wad ∧
  wad < dimword (:256) ∧
  access_slot_check dom (SK addr (balance_slot_key tx.from))
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = SOME Reverted ∧
    result.output = [] ∧
    result.logs = [] ∧
    (∀a. (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    (lookup_account addr accounts').code = contract_code ∧
    (lookup_account addr accounts').storage =
      (lookup_account addr accounts).storage ∧
    (blk.coinBase ≠ addr ⇒
     lookup_account addr accounts' = lookup_account addr accounts)
Proof
  PURE_REWRITE_TAC [zero_value_call_def]
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
  \\ mp_tac (Q.INST [‘p’ |-> ‘ctxt.msgParams’, ‘rb’ |-> ‘s.rollback’,
                     ‘d’ |-> ‘dom’, ‘rd’ |-> ‘[]’, ‘returnCode’ |-> ‘F’,
                     ‘txParams’ |-> ‘s.txParams’, ‘callee’ |-> ‘addr’,
                     ‘s'’ |-> ‘s with rollback updated_by
                       (λr. r with accounts updated_by
                              transfer_value tx.from addr tx.value)’]
                    revert_lift)
  \\ impl_tac
  >- (
    simp_tac pure_ss [evm2set_def, GSYM STAR_ASSOC]
    \\ simp[STAR_evm2set, STAR_evm_OriginalAccounts, STAR_CODE_POOL_evm2set,
            cond_STAR, SEP_T_def,
            transfer_value_zero, execution_state_component_equality,
            rollback_state_component_equality, fmap_entries_def,
            SIMP_RULE std_ss [APPEND] transfer_selector_calldata,
            DROP_APPEND, DROP_LENGTH_TOO_LONG, calldata_word, mask_and_w2w,
            balance_slot_key_bytes]
    \\ qpat_assum `lookup_account addr s.rollback.accounts = _`
         (fn th => rewrite_tac[th])
    \\ gas_bounds_tac
    \\ gvs[])
  \\ strip_tac
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ gvs[lookup_account_pay_transaction_gas, transfer_value_zero]
  \\ rw[account_state_component_equality]
QED

(* the same from the WETH_EVM relation, which the revert preserves, assuming
   the caller's balance slot is none of the slots 0-2 and, if the caller is
   untouched, no touched account's slot *)
Theorem WETH_EVM_transfer_revert_run_transaction:
  WETH_EVM addr ws accounts ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "transfer" [Address; Uint 256] ++
     enc (Tuple [Address; Uint 256]) (ListV [NumV (w2n dst); NumV wad]))
    2615 s ∧
  ws.balances tx.from < wad ∧ wad < dimword (:256) ∧
  (tx.from ∉ ws.touched ⇒
   balance_slot_key tx.from ∉ IMAGE balance_slot_key ws.touched) ∧
  balance_slot_key tx.from ∉ {0w; 1w; 2w} ∧
  access_slot_check dom (SK addr (balance_slot_key tx.from)) ∧
  blk.coinBase ≠ addr
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = SOME Reverted ∧
    result.output = [] ∧
    result.logs = [] ∧
    (∀a. a ≠ addr ⇒
         (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    WETH_EVM addr ws accounts'
Proof
  strip_tac
  \\ `lookup_storage (balance_slot_key tx.from)
        (lookup_account addr accounts).storage = n2w (ws.balances tx.from)`
  by (qpat_x_assum `WETH_EVM _ _ _` mp_tac
      \\ simp_tac std_ss [WETH_EVM_def, LET_THM] \\ strip_tac
      \\ first_x_assum irule \\ gvs[] \\ metis_tac[])
  \\ `ws.balances tx.from < dimword (:256)`
  by (qpat_x_assum `WETH_EVM _ _ _` mp_tac
      \\ simp[WETH_EVM_def, wf_WETH_state_def])
  \\ `w2n (lookup_storage (balance_slot_key tx.from)
             (lookup_account addr accounts).storage) < wad`
  by gvs[]
  \\ `(lookup_account addr accounts).code = contract_code`
  by gvs[WETH_EVM_def]
  \\ drule_all weth_transfer_revert_run_transaction \\ strip_tac
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ `lookup_account addr accounts' = lookup_account addr accounts` by gvs[]
  \\ rpt conj_tac \\ TRY (first_assum ACCEPT_TAC)
  >- (gen_tac \\ strip_tac \\ asm_rewrite_tac[])
  \\ qpat_x_assum `WETH_EVM _ _ _` mp_tac
  \\ simp_tac std_ss [WETH_EVM_def, LET_THM]
  \\ pop_assum SUBST1_TAC
  \\ asm_rewrite_tac[]
  \\ strip_tac
  \\ asm_simp_tac std_ss []
  \\ conj_tac \\ first_assum ACCEPT_TAC
QED
