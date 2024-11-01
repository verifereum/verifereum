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
   ; toDelete  : address list
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
   ; toDelete : address list
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
   ; toDelete  : address list
   ; outputTo  : return_destination
   ; static    : bool
   |>
End

Definition base_cost_def:
  base_cost = 21000n
End

Definition create_cost_def:
  create_cost = 32000n
End

Definition call_data_cost_def:
  call_data_cost is_zero =
  if is_zero then 4n else 16
End

Definition init_code_word_cost_def:
  init_code_word_cost = 2n
End

Definition code_deposit_cost_def:
  code_deposit_cost = 200n
End

Definition warm_access_cost_def:
  warm_access_cost = 100n
End

Definition cold_sload_cost_def:
  cold_sload_cost = 2100n
End

Definition cold_access_cost_def:
  cold_access_cost = 2600n
End

Definition memory_cost_per_word_def:
  memory_cost_per_word = 3n
End

Definition memory_copy_cost_def:
  memory_copy_cost = 3n
End

Definition exp_per_byte_cost_def:
  exp_per_byte_cost = 50n
End

Definition keccak256_per_word_cost_def:
  keccak256_per_word_cost = 6n
End

Definition storage_set_cost_def:
  storage_set_cost = 20000n
End

Definition storage_update_cost_def:
  storage_update_cost = 5000n
End

Definition storage_clear_refund_def:
  storage_clear_refund = 4800n
End

Definition log_topic_cost_def:
  log_topic_cost = 375n
End

Definition log_data_cost_def:
  log_data_cost = 8n
End

Definition new_account_cost_def:
  new_account_cost = 25000n
End

Definition call_value_cost_def:
  call_value_cost = 9000n
End

Definition self_destruct_new_account_cost_def:
  self_destruct_new_account_cost = 25000n
End

Definition word_size_def:
  word_size byteSize = (byteSize + 31) DIV 32
End

Definition call_stipend_def:
  call_stipend = 2300n
End

Definition is_code_dest_def:
  is_code_dest (Code _ ) = T ∧
  is_code_dest _ = F
End

Definition access_list_address_cost_def:
  access_list_address_cost = 2400n
End

Definition access_list_storage_key_cost_def:
  access_list_storage_key_cost = 1900n
End

Definition intrinsic_cost_def:
  intrinsic_cost accessList p =
  let isCreate = is_code_dest p.outputTo in
  let data = if isCreate then p.code else p.data in
  base_cost
  + SUM (MAP (λb. call_data_cost (b = 0w)) data)
  + (if isCreate
     then create_cost + init_code_word_cost * (word_size $ LENGTH data)
     else 0)
  + access_list_address_cost * LENGTH accessList
  + access_list_storage_key_cost * SUM (MAP (λx. fCARD x.keys) accessList)
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
  initial_call_params callee (ctxt: call_context) t =
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
   ; toDelete  := ctxt.toDelete
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
  initial_access_sets coinBase callee t =
  <| addresses   :=
       fUNION (
         fINSERT t.from $ fINSERT callee $ fINSERT coinBase $
         fIMAGE (λe. e.account) $ fset_ABS t.accessList
       ) precompile_addresses
   ; storageKeys := fBIGUNION
                      (fIMAGE (λe. fIMAGE (SK e.account) e.keys)
                              (fset_ABS t.accessList))
   |>
End

Definition apply_intrinsic_cost_def:
  apply_intrinsic_cost accessList c =
  c with callParams updated_by (λp.
    p with gasLimit updated_by (λl.
      l - intrinsic_cost accessList p
    )
  )
End

Theorem wf_context_apply_intrinsic_cost[simp]:
  wf_context (apply_intrinsic_cost a c) =
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
  (* TODO: ensure sender has no code *)
  if sender.nonce ≠ t.nonce ∨ t.nonce ≥ 2 ** 64 - 1 then NONE else
  if sender.balance < fee + t.value then NONE else
  let updatedSender = sender with <|
    nonce := SUC sender.nonce;
    balance := sender.balance - fee
  |> in
  let accounts = update_account t.from updatedSender a in
  let callee = callee_from_tx_to t.from sender.nonce t.to in
  let accesses = initial_access_sets b.coinBase callee t in
  let code = case t.to of
                  SOME addr => (lookup_account addr a).code
                | NONE => t.data in
  let rd = if IS_SOME t.to then empty_return_destination else Code callee in
  let ctxt = <| code := code; accounts := accounts; accesses := accesses
              ; toDelete := []; outputTo := rd; static := F |> in
  SOME $
  <| contexts := [apply_intrinsic_cost t.accessList $
                  initial_context callee ctxt t]
   ; txParams := initial_tx_params c h b t
   ; accesses := accesses
   ; accounts := accounts
   ; toDelete := []
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
