# TASK: Prove WETH read-only getters and preserve the extended state relation

## Meta
Status: planned
Priority: P1
Created: 2026-10-29
Location: examples

## Theorem Statement (FROZEN)

```sml
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
```

Do not modify these statements. Prove them as-is, or produce a counterexample.

The approved supporting definitions are frozen as well:

```sml
Definition allowance_slot_key_def:
  allowance_slot_key (owner:address) (spender:address): bytes32 =
    word_of_bytes_be $ Keccak_256_w64 $
      REVERSE (word_to_bytes_le (w2w spender : bytes32)) ++
      REVERSE (word_to_bytes_le
        (word_of_bytes_be (Keccak_256_w64
          (REVERSE (word_to_bytes_le (w2w owner : bytes32)) ++
           REVERSE (word_to_bytes_le (4w:bytes32)))) : bytes32))
End
Definition empty_WETH_state_def:
  empty_WETH_state = <|
    balances := K 0
  ; allowances := K (K 0)
  ; locked := 0
  ; touched := {}
  ; allowances_touched := {}
  |>
End
Definition wf_WETH_state_def:
  wf_WETH_state ws ⇔
    { a | 0 < ws.balances a } SUBSET ws.touched ∧
    { p | 0 < ws.allowances (FST p) (SND p) } SUBSET ws.allowances_touched ∧
    (∀a. ws.balances a < 2 ** 256) ∧
    (∀owner spender. ws.allowances owner spender < 2 ** 256) ∧
    ws.locked < 2 ** 256 ∧
    total_balances ws ≤ ws.locked
End
Definition WETH_EVM_def:
  WETH_EVM addr ws a =
  let s = lookup_account addr a in
  wf_WETH_state ws ∧
  (∀a. balance_slot_key a ∉ {0w; 1w; 2w} ∧
       (a ∈ ws.touched ∨ balance_slot_key a ∉ IMAGE balance_slot_key ws.touched) ⇒
       lookup_storage (balance_slot_key a) s.storage = n2w (ws.balances a)) ∧
  (* Balance writes may mask an allowance slot on a hash collision. The
     separate touched-pair set stays unchanged during a balance transfer. *)
  (∀owner spender.
     allowance_slot_key owner spender ∉ {0w; 1w; 2w} ∧
     allowance_slot_key owner spender ∉ IMAGE balance_slot_key ws.touched ∧
     ((owner, spender) ∈ ws.allowances_touched ∨
      allowance_slot_key owner spender ∉
        IMAGE (λ(owner, spender). allowance_slot_key owner spender)
          ws.allowances_touched) ⇒
     lookup_storage (allowance_slot_key owner spender) s.storage =
       n2w (ws.allowances owner spender)) ∧
  lookup_storage 0w s.storage =
    0x577261707065642045746865720000000000000000000000000000000000001Aw ∧
  lookup_storage 1w s.storage =
    0x5745544800000000000000000000000000000000000000000000000000000008w ∧
  lookup_storage 2w s.storage = 18w ∧
  s.balance = ws.locked ∧
  s.code = contract_code ∧
  s.nonce = 1
End
```

The WETH_state datatype now has allowances : address -> address -> num and
allowances_touched : (address # address) set, independently of touched.
Do not alter these fields or their meanings.
All pre-existing theorem statements in examples/wrappedEther*Script.sml are
frozen; repair proofs affected by the changed definitions without changing
what they claim or assume. New internal helper statements may be designed
as needed.

## Completion Criteria

- Five frozen getter theorems proved without admissions.
- All existing wrappedEther, wrappedEtherName and wrappedEtherTransfer
  theorem proofs rebuilt successfully with their statements unchanged.
- No new axioms, cheats, skipped proofs, timeout increases or weakened checks.
- Any false statement is reported with a concrete counterexample and a
  sufficient correction; do not silently change its hypotheses.
- All supporting machinery is built and validated before using it in a
  final proof; share helpers only where their consumers need them.

## Build

Run from the project root:

```sh
holbuild --max-heap 9000 -j4 build wrappedEtherTheory wrappedEtherNameTheory wrappedEtherTransferTheory wrappedEtherGettersTheory
```

Keep the existing holproject.toml tactic_timeout (30 seconds) and proof-step
instrumentation enabled. Build only these touched targets and their dependencies.
Do not run EEST, the full project build, Holmake or native HOL builds.

## Background

The WETH example has a deployment correctness theorem, a name() getter theorem
and success/revert transfer theorems. The abstract allowance map previously had
only one address argument and no storage relation. The extended relation now
covers nested owner/spender mapping storage, and the five remaining read-only
entry points need proofs over run_transaction. Their postconditions preserve
all account code, storage and nonces relative to the call's initial rollback
state; transaction fee changes to ETH balances remain possible.

## Domain Constraints

- Scope: examples/wrappedEther*Script.sml, and the root theory import already
  added for wrappedEtherGettersTheory. Do not edit prog, semantics or tooling.
- Keep definitions and frozen statements unchanged. No extra hypotheses.
- No TRY/ORELSE around proof search (including metis_tac).
- Never increase or disable tactic timeouts or pass --skip-proof-steps.
- Use consistent quotation delimiters within each script.
- Commit milestones locally; do not push or open a PR.
- Every commit ends with the exact trailer: Bot: sol (OpenAI GPT-6.1 Sol)
- Keep task journals, scratch probes and .alan state out of source commits.
- Temporary probes/admissions must be removed before completion.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Frozen targets | examples/wrappedEtherGettersScript.sml | Five transaction getter theorems |
| Contract and invariant | examples/wrappedEtherScript.sml | contract_code, WETH_EVM, deployment and saved block summaries |
| Getter example | examples/wrappedEtherNameScript.sml | Composed name path and transaction lift |
| Transfer example | examples/wrappedEtherTransferScript.sml | ABI arguments, generic calldata facts, invariant preservation and revert proof |
| Branch composer example | examples/wrappedEtherBranchesScript.sml | Existing branch composition client |
| Decompiler interface | prog/evmDecompLib.sig | Block composition APIs |
| Decompiler implementation | prog/evmDecompLib.sml | Summary composition and memory simplification |
| SPEC and lifting | prog/vfmProgScript.sml | SPEC_to_run_transaction, zero_value_call, initial_state_contract |
| Initial state | spec/vfmContextScript.sml | initial_state and transaction setup |
| ABI | util/contractABIScript.sml | function_selector and enc |
| Build manifest | holproject.toml | HOL dependency and tactic timeout |

## Notes

The existing name and transfer files are examples, not requirements to copy
large blocks mechanically. Use their existing proved facts when applicable.
