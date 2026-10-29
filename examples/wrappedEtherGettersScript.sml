(* Read-only WETH entry points over run_transaction. *)
Theory wrappedEtherGetters
Ancestors
  arithmetic list rich_list combin pair pred_set byte cv_std words
  vfmTypes vfmConstants vfmState vfmContext vfmExecution vfmExecutionProp
  vfmBuffer set_sep prog vfmProg contractABI wrappedEther wrappedEtherName
Libs
  dep_rewrite wordsLib cv_transLib evmDecompLib

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

