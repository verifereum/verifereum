open HolKernel boolLib bossLib Parse
     listTheory rich_listTheory pred_setTheory finite_setTheory
     byteTheory recursiveLengthPrefixTheory
     vfmConstantsTheory vfmTypesTheory vfmStateTheory
     vfmTransactionTheory vfmOperationTheory;

val () = new_theory "vfmContext";

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

Definition empty_return_destination_def:
  empty_return_destination = Memory <| offset := 0; size := 0 |>
End

Type transient_storage = “:address -> storage”

Definition empty_transient_storage_def:
  empty_transient_storage (a: address) = empty_storage
End

Datatype:
  rollback_state =
  <| accounts  : evm_accounts
   ; tStorage  : transient_storage
   ; accesses  : access_sets
   ; toDelete  : address list
   |>
End

Datatype:
  call_info =
  <| code      : byte list
   ; static    : bool
   ; outputTo  : return_destination
   ; rollback  : rollback_state
   |>
End

Datatype:
  message_parameters =
  <| caller    : address
   ; callee    : address
   ; parsed    : num |-> opname
   ; value     : num
   ; gasLimit  : num
   ; data      : byte list
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
   ; addRefund  : num
   ; subRefund  : num
   ; logs       : event list
   ; callInfo   : call_info
   ; msgParams  : message_parameters
   |>
End

Definition wf_context_def:
  wf_context c ⇔
    LENGTH c.stack ≤ stack_limit
End

Datatype:
  execution_state =
  <| contexts : context list
   ; txParams : transaction_parameters
   ; rollback : rollback_state
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

Definition is_code_dest_def:
  is_code_dest (Code _ ) = T ∧
  is_code_dest _ = F
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

Definition address_for_create_def:
  address_for_create (address: address) nonce : address =
    let rlpSender = rlp_bytes $ word_to_bytes address T in
    let rlpNonce = rlp_bytes $ if nonce = 0n then [] else
                   MAP n2w $ REVERSE $ n2l 256 $ nonce in
    let rlpBytes = rlp_list $ rlpSender ++ rlpNonce in
    let hash = word_of_bytes T (0w:bytes32) $ Keccak_256_w64 $ rlpBytes in
    w2w hash
End

Definition callee_from_tx_to_def:
  callee_from_tx_to sender nonce NONE = address_for_create sender nonce ∧
  callee_from_tx_to sender nonce (SOME address) = address
End

Definition initial_msg_params_def:
  initial_msg_params callee code t =
  <| caller    := t.from
   ; callee    := callee
   ; parsed    := parse_code 0 FEMPTY code
   ; value     := t.value
   ; data      := if t.to = NONE then [] else t.data
   ; gasLimit  := t.gasLimit
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
  initial_context callee call t =
  <| stack      := []
   ; memory     := []
   ; pc         := 0
   ; jumpDest   := NONE
   ; returnData := []
   ; gasUsed    := 0
   ; addRefund  := 0
   ; subRefund  := 0
   ; logs       := []
   ; callInfo   := call
   ; msgParams  := initial_msg_params callee call.code t
   |>
End

Theorem initial_context_simp[simp]:
  (initial_context callee c t).stack = [] ∧
  (initial_context callee c t).memory = [] ∧
  (initial_context callee c t).pc = 0 ∧
  (initial_context callee c t).jumpDest = NONE ∧
  (initial_context callee c t).returnData = [] ∧
  (initial_context callee c t).gasUsed = 0 ∧
  (initial_context callee c t).addRefund = 0 ∧
  (initial_context callee c t).subRefund = 0 ∧
  (initial_context callee c t).logs = [] ∧
  (initial_context callee c t).msgParams  = initial_msg_params callee c.code t
Proof
  rw[initial_context_def]
QED

Theorem wf_initial_context[simp]:
  wf_context (initial_context callee c t)
Proof
  rw[wf_context_def]
QED

Definition wf_state_def:
  wf_state s ⇔
    s.contexts ≠ [] ∧
    LENGTH s.contexts ≤ context_limit ∧
    EVERY wf_context s.contexts ∧
    wf_accounts s.rollback.accounts
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
         fset_ABS $ MAP (λe. e.account) t.accessList
       ) precompile_addresses
   ; storageKeys := fBIGUNION $ fset_ABS $
                      (MAP (λe. fset_ABS $ MAP (SK e.account) e.keys)
                           t.accessList)
   |>
End

Definition intrinsic_cost_def:
  intrinsic_cost accessList p =
  let isCreate = is_code_dest p.callInfo.outputTo in
  let data = if isCreate then p.callInfo.code else p.msgParams.data in
  base_cost
  + SUM (MAP (λb. call_data_cost (b = 0w)) data)
  + (if isCreate
     then create_cost + init_code_word_cost * (word_size $ LENGTH data)
     else 0)
  + access_list_address_cost * LENGTH accessList
  + access_list_storage_key_cost * SUM (MAP (λx. LENGTH x.keys) accessList)
End

Definition apply_intrinsic_cost_def:
  apply_intrinsic_cost accessList c =
  c with msgParams updated_by (λp.
    p with gasLimit updated_by (λl.
      l - intrinsic_cost accessList c
    )
  )
End

Theorem wf_context_apply_intrinsic_cost[simp]:
  wf_context (apply_intrinsic_cost a c) =
  wf_context c
Proof
  rw[apply_intrinsic_cost_def, wf_context_def]
QED

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
  let rb = <| accounts := accounts; accesses := accesses;
              tStorage := empty_transient_storage; toDelete := [] |> in
  let call = <| code := code; static := F; outputTo := rd; rollback := rb |> in
  SOME $
  <| contexts := [apply_intrinsic_cost t.accessList $
                  initial_context callee call t]
   ; txParams := initial_tx_params c h b t
   ; rollback := rb
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

val () = export_theory();
