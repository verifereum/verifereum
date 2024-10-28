open HolKernel boolLib bossLib Parse
     listTheory rich_listTheory pred_setTheory finite_setTheory
     byteTheory recursiveLengthPrefixTheory keccakTheory
     vfmTypesTheory vfmStateTheory vfmTransactionTheory vfmOperationTheory;

val _ = new_theory "vfmContext";

Datatype:
  transaction_parameters =
  <| origin         : address
   ; gasPrice       : num
   ; baseFeePerGas  : num
   ; blockNumber    : num
   ; blockTimeStamp : num
   ; blockCoinBase  : address
   ; blockGasLimit  : num
   ; prevRandao     : bytes32
   ; prevHashes     : bytes32 list
   ; chainId        : num
   |>
End

Datatype:
  storage_key = SK address bytes32
End

Datatype:
  access_sets =
  <| addresses   : address fset
   ; storageKeys : storage_key fset
   |>
End

Datatype:
  memory_range =
  <| offset : num
   ; size   : num
   |>
End

Datatype:
  return_destination =
  | Memory memory_range
  | Code address
End

Datatype:
  call_parameters =
  <| caller    : address
   ; callee    : address
   ; code      : byte list
   ; parsed    : num |-> opname
   ; value     : num
   ; static    : bool
   ; gasLimit  : num
   ; data      : byte list
   ; outputTo  : return_destination
   (* values at the start of the call, for rollback *)
   ; accounts  : evm_accounts
   ; accesses  : access_sets
   |>
End

Datatype:
  context =
  <| stack      : bytes32 list
   ; memory     : byte list
   ; pc         : num
   ; jumpDest   : num option
   ; returnData : byte list
   ; gasUsed    : num
   ; gasRefund  : num
   ; logs       : event list
   ; callParams : call_parameters
   |>
End

Definition stack_limit_def[simp]:
  stack_limit = 1024n
End

Definition context_limit_def[simp]:
  context_limit = 1024n
End

Definition wf_context_def:
  wf_context c ⇔
    LENGTH c.stack ≤ stack_limit
End

Datatype:
  execution_state =
  <| contexts : context list
   ; txParams : transaction_parameters
   ; accesses : access_sets
   ; accounts : evm_accounts
   |>
End

Datatype:
  block =
  <| baseFeePerGas         : num
   ; number                : num
   ; timeStamp             : num
   ; coinBase              : address
   ; gasLimit              : num
   ; prevRandao            : bytes32
   ; hash                  : bytes32
   ; parentBeaconBlockRoot : bytes32
   ; transactions          : transaction list
   |>
End

Datatype:
  call_context =
  <| code      : byte list
   ; accounts  : evm_accounts
   ; accesses  : access_sets
   ; outputTo  : return_destination
   ; static    : bool
   |>
End

Definition base_cost_def:
  base_cost = 21000n
End

Definition call_data_cost_def:
  call_data_cost is_zero =
  if is_zero then 4n else 16
End

Definition intrinsic_cost_def:
  intrinsic_cost (data: byte list) =
  base_cost + SUM (MAP (λb. call_data_cost (b = 0w)) data)
End

Definition parse_code_def:
  parse_code pc m code =
  if NULL code then m else
  let op = case parse_opcode code of
                NONE => Invalid
              | SOME op => op in
  let n = LENGTH $ opcode op in
  parse_code (pc + n) (m |+ (pc, op)) (DROP n code)
Termination
  WF_REL_TAC`measure (LENGTH o SND o SND)`
  \\ rw[LENGTH_DROP, LENGTH_NOT_NULL]
End

(* TODO: move? *)
Definition Keccak_256_bytes_def:
  Keccak_256_bytes (bs:word8 list) : word8 list =
    MAP bools_to_word $ chunks 8 $
    Keccak_256 $
    MAP ((=) 1) $ FLAT $
    MAP (PAD_RIGHT 0 8 o word_to_bin_list) bs
End

Definition address_for_create_def:
  address_for_create (address: address) nonce : address =
    let rlpSender = rlp_bytes $ word_to_bytes address T in
    let rlpNonce = rlp_bytes $ if nonce = 0n then [] else
                   MAP n2w $ REVERSE $ n2l 256 $ nonce in
    let rlpBytes = rlp_list $ rlpSender ++ rlpNonce in
    let hash = word_of_bytes T (0w:bytes32) $ Keccak_256_bytes $ rlpBytes in
    w2w hash
End

Definition lookup_account_def:
  lookup_account address (accounts: evm_accounts) = accounts address
End

Definition update_account_def:
  update_account address new_account (accounts: evm_accounts) =
    (address =+ new_account) accounts
End

Definition callee_from_tx_to_def:
  callee_from_tx_to sender nonce NONE = address_for_create sender nonce ∧
  callee_from_tx_to sender nonce (SOME address) = address
End

Definition initial_call_params_def:
  initial_call_params callee ctxt t =
  <| caller    := t.from
   ; callee    := callee
   ; code      := ctxt.code
   ; parsed    := parse_code 0 FEMPTY ctxt.code
   ; value     := t.value
   ; static    := ctxt.static
   ; data      := if t.to = NONE then [] else t.data
   ; gasLimit  := t.gasLimit
   ; accounts  := ctxt.accounts
   ; accesses  := ctxt.accesses
   ; outputTo  := ctxt.outputTo
   |>
End

Definition initial_tx_params_def:
  initial_tx_params c h b t =
  <| origin         := t.from
   ; gasPrice       := t.gasPrice
   ; baseFeePerGas  := b.baseFeePerGas
   ; blockNumber    := b.number
   ; blockTimeStamp := b.timeStamp
   ; blockCoinBase  := b.coinBase
   ; blockGasLimit  := b.gasLimit
   ; prevRandao     := b.prevRandao
   ; prevHashes     := h
   ; chainId        := c
   |>
End

Definition initial_context_def:
  initial_context callee ctxt t =
  <| stack      := []
   ; memory     := []
   ; pc         := 0
   ; jumpDest   := NONE
   ; returnData := []
   ; gasUsed    := 0
   ; gasRefund  := 0
   ; logs       := []
   ; callParams := initial_call_params callee ctxt t
   |>
End

Theorem initial_call_params_simp[simp]:
  (initial_call_params callee ctxt t).code = ctxt.code ∧
  (initial_call_params callee ctxt t).gasLimit = t.gasLimit ∧
  (initial_call_params callee ctxt t).outputTo = ctxt.outputTo
  (* TODO: as needed *)
Proof
  rw[initial_call_params_def]
QED

Theorem initial_context_simp[simp]:
  (initial_context callee ctxt t).stack = [] ∧
  (initial_context callee ctxt t).memory = [] ∧
  (initial_context callee ctxt t).pc = 0 ∧
  (initial_context callee ctxt t).jumpDest = NONE ∧
  (initial_context callee ctxt t).returnData = [] ∧
  (initial_context callee ctxt t).gasUsed = 0 ∧
  (initial_context callee ctxt t).gasRefund = 0 ∧
  (initial_context callee ctxt t).logs = [] ∧
  (initial_context callee ctxt t).callParams = initial_call_params callee ctxt t
Proof
  rw[initial_context_def]
QED

Theorem wf_initial_context[simp]:
  wf_context (initial_context callee ctxt t)
Proof
  rw[wf_context_def]
QED

Definition wf_state_def:
  wf_state s ⇔
    s.contexts ≠ [] ∧
    LENGTH s.contexts ≤ context_limit ∧
    EVERY wf_context s.contexts ∧
    wf_accounts s.accounts
End

Definition precompile_addresses_def:
  precompile_addresses : address fset =
  fset_ABS (GENLIST (n2w o SUC) 10)
End

Definition initial_access_sets_def:
  initial_access_sets callee t =
  <| addresses   :=
       fUNION (
         fINSERT t.from $ fINSERT callee $
         fIMAGE (λe. e.account) $ fset_ABS t.accessList
       ) precompile_addresses
   ; storageKeys := fBIGUNION
                      (fIMAGE (λe. fIMAGE (SK e.account) e.keys)
                              (fset_ABS t.accessList))
   |>
End

Definition apply_intrinsic_cost_def:
  apply_intrinsic_cost c =
  c with callParams updated_by (λp.
    p with gasLimit updated_by (λl.
      l - intrinsic_cost p.data
    )
  )
End

Theorem wf_context_apply_intrinsic_cost[simp]:
  wf_context (apply_intrinsic_cost c) =
  wf_context c
Proof
  rw[apply_intrinsic_cost_def, wf_context_def]
QED

Definition empty_return_destination_def:
  empty_return_destination = Memory <| offset := 0; size := 0 |>
End

Definition initial_state_def:
  initial_state c h b a t =
  let sender = lookup_account t.from a in
  let fee = t.gasLimit * t.gasPrice in (* TODO: add blob gas fee *)
  if sender.nonce ≠ t.nonce ∨ t.nonce ≥ 2 ** 64 - 1 then NONE else
  if sender.balance < fee + t.value then NONE else
  let updatedSender = sender with <|
    nonce := SUC sender.nonce;
    balance := sender.balance - fee
  |> in
  let accounts = update_account t.from updatedSender a in
  let callee = callee_from_tx_to t.from sender.nonce t.to in
  let acc = initial_access_sets callee t in
  let code = case t.to of
                  SOME addr => (lookup_account addr a).code
                | NONE => t.data in
  let rd = if IS_SOME t.to then empty_return_destination else Code callee in
  let ctxt = <| code := code; accounts := accounts; accesses := acc
              ; outputTo := rd; static := F |> in
  SOME $
  <| contexts := [apply_intrinsic_cost $ initial_context callee ctxt t]
   ; txParams := initial_tx_params c h b t
   ; accesses := acc
   ; accounts := accounts
   |>
End

Theorem wf_initial_state:
  wf_accounts a ∧ initial_state c h b a t = SOME s
  ⇒
  wf_state s
Proof
  rw[wf_accounts_def, wf_state_def, initial_state_def,
     update_account_def, lookup_account_def] \\ rw[]
  \\ gs[wf_account_state_def, combinTheory.APPLY_UPDATE_THM]
  \\ rw[]
QED

val _ = export_theory();
