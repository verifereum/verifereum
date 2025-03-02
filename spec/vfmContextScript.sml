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
  message_parameters =
  <| caller    : address
   ; callee    : address
   ; code      : byte list
   ; parsed    : num |-> opname
   ; value     : num
   ; gasLimit  : num
   ; data      : byte list
   ; static    : bool
   ; outputTo  : return_destination
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
   ; msgParams  : message_parameters
   |>
End

Datatype:
  domain =
  <| addresses:    address fset
   ; storageKeys:  storage_key fset
   ; fullStorages: address fset
   |>
End

Definition empty_domain_def:
  empty_domain = <|
    addresses := fEMPTY
  ; storageKeys := fEMPTY
  ; fullStorages := fEMPTY
  |>
End

Datatype:
  domain_mode =
    Enforce domain
  | Collect domain
End

Datatype:
  execution_state =
  <| contexts : (context # rollback_state) list
   ; txParams : transaction_parameters
   ; rollback : rollback_state
   ; msdomain : domain_mode
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
  initial_msg_params callee code static rd t =
  <| caller    := t.from
   ; callee    := callee
   ; code      := code
   ; parsed    := parse_code 0 FEMPTY code
   ; value     := t.value
   ; data      := if t.to = NONE then [] else t.data
   ; gasLimit  := t.gasLimit
   ; static    := static
   ; outputTo  := rd
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
  initial_context callee code static rd t =
  <| stack      := []
   ; memory     := []
   ; pc         := 0
   ; jumpDest   := NONE
   ; returnData := []
   ; gasUsed    := 0
   ; addRefund  := 0
   ; subRefund  := 0
   ; logs       := []
   ; msgParams  := initial_msg_params callee code static rd t
   |>
End

Theorem initial_context_simp[simp]:
  (initial_context fr c s rd t).stack = [] ∧
  (initial_context fr c s rd t).memory = [] ∧
  (initial_context fr c s rd t).pc = 0 ∧
  (initial_context fr c s rd t).jumpDest = NONE ∧
  (initial_context fr c s rd t).returnData = [] ∧
  (initial_context fr c s rd t).gasUsed = 0 ∧
  (initial_context fr c s rd t).addRefund = 0 ∧
  (initial_context fr c s rd t).subRefund = 0 ∧
  (initial_context fr c s rd t).logs = [] ∧
  (initial_context fr c s rd t).msgParams  = initial_msg_params fr c s rd t
Proof
  rw[initial_context_def]
QED

Definition precompile_addresses_def:
  precompile_addresses : address fset =
  fset_ABS (GENLIST (n2w o SUC) 10)
End

Definition initial_access_sets_def:
  initial_access_sets coinBase callee t : access_sets =
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
  let isCreate = is_code_dest p.outputTo in
  let data = if isCreate then p.code else p.data in
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
      l - intrinsic_cost accessList p
    )
  )
End

Definition initial_rollback_def:
  initial_rollback accounts accesses =
  <| accounts := accounts; accesses := accesses;
     tStorage := empty_transient_storage; toDelete := [] |>
End

Definition pre_transaction_updates_def:
  pre_transaction_updates a t =
  let sender = lookup_account t.from a in
  let fee = t.gasLimit * t.gasPrice in (* TODO: add blob gas fee *)
  (* TODO: ensure sender has no code *)
  if sender.nonce ≠ t.nonce ∨ t.nonce ≥ 2 ** 64 - 1 then NONE else
  if sender.balance < fee + t.value then NONE else
  let updatedSender = sender with <|
    nonce := SUC sender.nonce;
    balance := sender.balance - fee
  |> in
  SOME $ update_account t.from updatedSender a
End

Definition code_from_tx_def:
  code_from_tx a t =
  case t.to of
    SOME addr => (lookup_account addr a).code
  | NONE => t.data
End

Definition initial_state_def:
  initial_state dom static chainId prevHashes blk accs tx =
  case pre_transaction_updates accs tx of NONE => NONE |
  SOME accounts =>
    let callee = callee_from_tx_to tx.from tx.nonce tx.to in
    let accesses = initial_access_sets blk.coinBase callee tx in
    let code = code_from_tx accs tx in
    let rd = if IS_SOME tx.to then empty_return_destination else Code callee in
    let rb = initial_rollback accounts accesses in
    let ctxt = initial_context callee code static rd tx in
    SOME $
    <| contexts := [(apply_intrinsic_cost tx.accessList $ ctxt, rb)]
     ; txParams := initial_tx_params chainId prevHashes blk tx
     ; rollback := rb
     ; msdomain := dom
     |>
End

val () = export_theory();
