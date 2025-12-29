Theory vfmContext
Ancestors
  list rich_list
  secp256k1
  vfmTypes vfmConstants vfmOperation vfmState vfmTransaction

Datatype:
  transaction_parameters =
  <| origin         : address
   ; gasPrice       : num
   ; baseFeePerGas  : num
   ; baseFeePerBlobGas : num
   ; blockNumber    : num
   ; blockTimeStamp : num
   ; blockCoinBase  : address
   ; blockGasLimit  : num
   ; prevRandao     : bytes32
   ; prevHashes     : bytes32 list
   ; blobHashes     : bytes32 list
   ; chainId        : num
   ; authRefund     : num
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
  withdrawal = <|
    withdrawalIndex: num;
    validatorIndex: num;
    withdrawalAddress: address;
    withdrawalAmount: num
  |>
End

Datatype:
  block =
  <| baseFeePerGas         : num
   ; excessBlobGas         : num
   ; gasUsed               : num
   ; blobGasUsed           : num
   ; number                : num
   ; timeStamp             : num
   ; coinBase              : address
   ; gasLimit              : num
   ; prevRandao            : bytes32
   ; hash                  : bytes32
   ; parentBeaconBlockRoot : bytes32
   ; requestsHash          : bytes32
   ; stateRoot             : bytes32
   ; withdrawalsRoot       : bytes32
   ; transactions          : transaction list
   ; withdrawals           : withdrawal list
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

Definition fake_exponential_def:
  fake_exponential f n d =
  (SND $ SND $
     WHILE (λ(a,i,r). 0 < a)
     (λ(a,i,r). ((a * n) DIV (d * i), i + 1, r + a))
     (f * d, 1, 0))
  DIV d
End

Definition base_fee_per_blob_gas_def:
  base_fee_per_blob_gas excessBlobGas =
    fake_exponential
      min_base_fee_per_blob_gas
      excessBlobGas
      blob_base_fee_update_fraction
End

Definition initial_tx_params_def:
  initial_tx_params c h b t ar =
  <| origin         := t.from
   ; gasPrice       := t.gasPrice
   ; baseFeePerGas  := b.baseFeePerGas
   ; baseFeePerBlobGas := base_fee_per_blob_gas b.excessBlobGas
   ; blockNumber    := b.number
   ; blockTimeStamp := b.timeStamp
   ; blockCoinBase  := b.coinBase
   ; blockGasLimit  := b.gasLimit
   ; prevRandao     := b.prevRandao
   ; prevHashes     := h
   ; blobHashes     := t.blobVersionedHashes
   ; chainId        := c
   ; authRefund     := ar
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
  fset_ABS (0x100w :: GENLIST (n2w o SUC) 17)
End

Definition delegation_prefix_def:
  delegation_prefix : byte list = [0xEFw; 0x01w; 0x00w]
End

Definition is_delegation_def:
  is_delegation (code : byte list) ⇔
    LENGTH code = 23 ∧ TAKE 3 code = delegation_prefix
End

Definition make_delegation_def:
  make_delegation (addr : address) : byte list =
    delegation_prefix ++ word_to_bytes addr T
End

Definition get_delegate_def:
  get_delegate (code : byte list) : address option =
    if is_delegation code
    then SOME (word_of_bytes T 0w (DROP 3 code))
    else NONE
End

Definition per_auth_base_cost_def:
  per_auth_base_cost = 12500n
End

Definition process_authorization_def:
  process_authorization chainId (auth: authorization) (accs, accesses: access_sets, refund) =
    let authority = auth.authority in
    let delegate = auth.delegate in
    let authChainId = auth.authChainId in
    let authNonce = auth.authNonce in
    let authS = auth.authS in
    if 2 * authS > secp256k1N then (accs, accesses, refund) else
    if authority = 0w then (accs, accesses, refund) else
    if authChainId ≠ 0 ∧ authChainId ≠ chainId then (accs, accesses, refund) else
    if authNonce ≥ 2 ** 64 - 1 then (accs, accesses, refund) else
    let newAccesses = accesses with addresses updated_by (λa. fINSERT authority a) in
    let acc = lookup_account authority accs in
    if ¬NULL acc.code ∧ ¬is_delegation acc.code then (accs, newAccesses, refund) else
    if acc.nonce ≠ authNonce then (accs, newAccesses, refund) else
    let newCode = if delegate = 0w then [] else make_delegation delegate in
    let newAcc = acc with <| code := newCode; nonce := SUC acc.nonce |> in
    let newAccs = update_account authority newAcc accs in
    let newRefund = if account_empty acc then refund
                    else refund + (new_account_cost - per_auth_base_cost) in
    (newAccs, newAccesses, newRefund)
End

Definition process_authorizations_def:
  process_authorizations chainId [] accs accesses refund = (accs, accesses, refund) ∧
  process_authorizations chainId (auth::auths) accs accesses refund =
    let (accs', accesses', refund') = process_authorization chainId auth (accs, accesses, refund) in
    process_authorizations chainId auths accs' accesses' refund'
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

Definition call_data_tokens_def:
  call_data_tokens data =
  SUM (MAP (λb. if b = 0w then 1n else 4) data)
End

Definition intrinsic_cost_def:
  intrinsic_cost accessList authListLen p =
  let isCreate = is_code_dest p.outputTo in
  let data = if isCreate then p.code else p.data in
    base_cost
    + SUM (MAP (λb. call_data_cost (b = 0w)) data)
    + (if isCreate
       then create_cost + init_code_word_cost * (word_size $ LENGTH data)
       else 0)
    + access_list_address_cost * LENGTH accessList
    + access_list_storage_key_cost * SUM (MAP (λx. LENGTH x.keys) accessList)
    + new_account_cost * authListLen
End

Definition apply_intrinsic_cost_def:
  apply_intrinsic_cost accessList authListLen c =
  let p = c.msgParams in
  let k = intrinsic_cost accessList authListLen p in
  let l = p.gasLimit in
  if l < k then NONE else SOME $
  c with msgParams updated_by (λp.
    p with gasLimit updated_by (λl. l - k))
End

Definition initial_rollback_def:
  initial_rollback accounts accesses =
  <| accounts := accounts; accesses := accesses;
     tStorage := empty_transient_storage; toDelete := [] |>
End

Definition versioned_hash_correct_def:
  versioned_hash_correct (h: bytes32) ⇔
    get_byte 0w h T = versioned_hash_version_kzg
End

Definition pre_transaction_updates_def:
  pre_transaction_updates a blobBaseFee t =
  if (case t.maxFeePerBlobGas of SOME mf =>
           mf < blobBaseFee ∨
           NULL t.blobVersionedHashes
         | _ => F) then NONE else
  if ¬EVERY versioned_hash_correct t.blobVersionedHashes then NONE else
  if t.gasLimit > 2 ** 24 then NONE else
  if IS_NONE t.to ∧ LENGTH t.data > 2 * max_code_size then NONE else
  let sender = lookup_account t.from a in
  if sender.balance < max_total_cost t then NONE else
  if ¬NULL sender.code ∧ ¬is_delegation sender.code then NONE else
  let fee = t.gasLimit * t.gasPrice +
            total_blob_gas t * blobBaseFee in
  if sender.nonce ≠ t.nonce ∨ t.nonce ≥ 2 ** 64 - 1 then NONE else
  if sender.balance < fee + t.value then NONE else
  let updatedSender = sender with <|
    nonce := SUC sender.nonce;
    balance := sender.balance - fee
  |> in
  SOME $ update_account t.from updatedSender a
End

Definition code_from_tx_def:
  code_from_tx a (c: access_sets) t =
  case t.to of
    SOME addr =>
      let code = (lookup_account addr a).code in
      (case get_delegate code of
         NONE => (code, c)
       | SOME delegate =>
           ((lookup_account delegate a).code,
            c with addresses updated_by (λa. fINSERT delegate a)))
  | NONE => (t.data, c)
End

Definition initial_state_def:
  initial_state dom static chainId prevHashes blk accs tx =
  case pre_transaction_updates
         accs (base_fee_per_blob_gas blk.excessBlobGas) tx
  of NONE => NONE | SOME accounts =>
    let callee = callee_from_tx_to tx.from tx.nonce tx.to in
    let baseAccesses = initial_access_sets blk.coinBase callee tx in
    let (postAuthAccounts, postAuthAccesses, authRefund) =
          process_authorizations chainId tx.authorizationList accounts baseAccesses 0 in
    let (code, accesses) = code_from_tx postAuthAccounts postAuthAccesses tx in
    let rd = if IS_SOME tx.to then empty_return_destination else Code callee in
    let rb = initial_rollback postAuthAccounts accesses in
    let ctxt = initial_context callee code static rd tx in
    let authListLen = LENGTH tx.authorizationList in
    case apply_intrinsic_cost tx.accessList authListLen ctxt of NONE => NONE | SOME ctxt =>
    SOME $
    <| contexts := [(ctxt, rb)]
     ; txParams := initial_tx_params chainId prevHashes blk tx authRefund
     ; rollback := rb
     ; msdomain := dom
     |>
End
