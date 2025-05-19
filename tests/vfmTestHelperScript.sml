open HolKernel boolLib bossLib Parse wordsLib dep_rewrite permLib
     pairTheory sortingTheory sumTheory wordsTheory
     vfmTypesTheory vfmExecutionTheory
     vfmStateTheory vfmContextTheory
     vfmOperationTheory vfmComputeTheory
     cv_transLib cv_typeTheory

val () = new_theory "vfmTestHelper";

Datatype:
  test_result
  = Passed
  | GenesisBlockDecodeFailure
  | GenesisBlockDecodeMismatch
  | GenesisHeaderMismatch bytes32
  | GenesisStateMismatch bytes32
  | ExpectedException string
  | ExceptionMismatch
  | UnexpectedException
  | BlockDecodeFailure
  | BlockDecodeMismatch
  | LastHashMismatch bytes32
  | StateMismatch
  | OutOfFuel
End

(* TODO: move to another theory? *)

Definition block_header_from_rlp_def:
  block_header_from_rlp rlp =
  if ¬is_RLPL rlp then NONE else
  let ls = dest_RLPL rlp in
  if ¬(LENGTH ls = 20 ∧ EVERY is_RLPB ls) then NONE else
  let coinbase   = dest_RLPB (EL  2 ls) in
  let stateRoot  = dest_RLPB (EL  3 ls) in
  let number     = dest_RLPB (EL  8 ls) in
  let gasLimit   = dest_RLPB (EL  9 ls) in
  let gasUsed    = dest_RLPB (EL 10 ls) in
  let timestamp  = dest_RLPB (EL 11 ls) in
  let prevRandao = dest_RLPB (EL 13 ls) in
  let baseFeePerGas = dest_RLPB (EL 15 ls) in
  let blobGasUsed   = dest_RLPB (EL 17 ls) in
  let excessBlobGas = dest_RLPB (EL 18 ls) in
  let parentBeaconBlockRoot = dest_RLPB (EL 19 ls) in
  (*
     parentHash;
     ommersHash;
     coinbase;
     stateRoot;
     transactionsRoot;
     receiptRoot;
     bloom;
     difficulty;
     number;
     gasLimit;
     gasUsed;
     timestamp;
     extraData;
     prevRandao;
     nonce;
     baseFeePerGas;
     withdrawalsRoot;
     blobGasUsed;
     excessBlobGas;
     parentBeaconBlockRoot
   *)
    SOME
    <| baseFeePerGas := num_of_be_bytes baseFeePerGas
     ; excessBlobGas := num_of_be_bytes excessBlobGas
     ; gasUsed       := num_of_be_bytes gasUsed
     ; blobGasUsed   := num_of_be_bytes blobGasUsed
     ; number        := num_of_be_bytes number
     ; timeStamp     := num_of_be_bytes timestamp
     ; coinBase      := word_of_bytes T 0w coinbase
     ; gasLimit      := num_of_be_bytes gasLimit
     ; prevRandao    := word_of_bytes T 0w prevRandao
     ; parentBeaconBlockRoot := word_of_bytes T 0w parentBeaconBlockRoot
     ; stateRoot     := word_of_bytes T 0w stateRoot
     (* not in header *)
     ; hash          := 0w
     ; transactions  := []
     ; withdrawals   := []
     |>
End

val block_header_from_rlp_pre_def =
  cv_auto_trans_pre block_header_from_rlp_def;

Theorem block_header_from_rlp_pre[cv_pre]:
  block_header_from_rlp_pre x
Proof
  rw[block_header_from_rlp_pre_def]
  \\ Cases_on`x` \\ gvs[]
  \\ strip_tac \\ gvs[]
QED

Definition withdrawal_from_rlp_def:
  withdrawal_from_rlp rlp =
  if ¬is_RLPL rlp then NONE else
  let ls = dest_RLPL rlp in
  if ¬(LENGTH ls = 4 ∧ EVERY is_RLPB ls) then NONE else
  let index = EL 0 ls in
  let validatorIndex = EL 1 ls in
  let address = EL 2 ls in
  let amount = EL 3 ls in
  SOME <|
    withdrawalIndex := num_of_be_bytes (dest_RLPB index)
  ; validatorIndex := num_of_be_bytes (dest_RLPB validatorIndex)
  ; withdrawalAddress := word_of_bytes T 0w (dest_RLPB address)
  ; withdrawalAmount := num_of_be_bytes (dest_RLPB amount)
  |>
End

val withdrawal_from_rlp_pre_def = cv_auto_trans_pre withdrawal_from_rlp_def;

Theorem withdrawal_from_rlp_pre[cv_pre]:
  withdrawal_from_rlp_pre x
Proof
  rw[withdrawal_from_rlp_pre_def]
  \\ strip_tac \\ gvs[]
QED

Definition access_list_entry_from_rlp_def:
  access_list_entry_from_rlp rlp =
  if ¬is_RLPL rlp then NONE else
  let ls = dest_RLPL rlp in
  if LENGTH ls ≠ 2 then NONE else
  let account = EL 0 ls in
  if ¬is_RLPB account then NONE else
  let account = word_of_bytes T 0w $ dest_RLPB account in
  let slots = EL 1 ls in
  if ¬is_RLPL slots then NONE else
  let ls = dest_RLPL slots in
  if ¬(EVERY is_RLPB ls) then NONE else
  let slots = MAP (word_of_bytes T 0w o dest_RLPB) ls in
  SOME <| account := account; keys := slots |>
End

val access_list_entry_from_rlp_pre_def =
  cv_auto_trans_pre access_list_entry_from_rlp_def;

Theorem access_list_entry_from_rlp_pre[cv_pre]:
  access_list_entry_from_rlp_pre x
Proof
  rw[access_list_entry_from_rlp_pre_def]
  \\ strip_tac \\ gvs[]
QED

Definition OPT_MMAP_access_list_entry_from_rlp_def:
  OPT_MMAP_access_list_entry_from_rlp [] = SOME [] ∧
  OPT_MMAP_access_list_entry_from_rlp (x::xs) =
  case access_list_entry_from_rlp x of NONE => NONE
     | SOME h =>
         case OPT_MMAP_access_list_entry_from_rlp xs of NONE => NONE
            | SOME t => SOME (h::t)
End

val () = cv_auto_trans OPT_MMAP_access_list_entry_from_rlp_def;

Theorem OPT_MMAP_access_list_entry_from_rlp_eq:
  OPT_MMAP_access_list_entry_from_rlp ls =
  OPT_MMAP access_list_entry_from_rlp ls
Proof
  Induct_on`ls` \\ rw[OPT_MMAP_access_list_entry_from_rlp_def]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
QED

Definition transaction1_from_rlp_def:
  transaction1_from_rlp rlp =
  if ¬is_RLPL rlp then NONE else
  let ls = dest_RLPL rlp in
  if LENGTH ls ≠ 11 then NONE else
  (* chain_id: U64 *)
  let nonce = EL 1 ls in
  if ¬is_RLPB nonce then NONE else
  let nonce = num_of_be_bytes $ dest_RLPB nonce in
  let gasPrice = EL 2 ls in
  if ¬is_RLPB gasPrice then NONE else
  let gasPrice = num_of_be_bytes $ dest_RLPB gasPrice in
  let gas = EL 3 ls in
  if ¬is_RLPB gas then NONE else
  let gas = num_of_be_bytes $ dest_RLPB gas in
  let to = EL 4 ls in
  if ¬is_RLPB to then NONE else
  let to = dest_RLPB to in
  let to = if LENGTH to = 0 then NONE
           else SOME $ word_of_bytes T 0w to in
  let value = EL 5 ls in
  if ¬is_RLPB value then NONE else
  let value = num_of_be_bytes $ dest_RLPB value in
  let data = EL 6 ls in
  if ¬is_RLPB data then NONE else
  let data = dest_RLPB data in
  let accessList = EL 7 ls in
  if ¬is_RLPL accessList then NONE else
  case OPT_MMAP access_list_entry_from_rlp (dest_RLPL accessList)
  of NONE => NONE |
  SOME accessList =>
  let yParity = EL 8 ls in
  let r = EL 9 ls in
  let s = EL 10 ls in
  SOME <|
      from := 0w (* TODO: ecrecover from yParity r s *)
    ; to := to
    ; data := data
    ; nonce := nonce
    ; value := value
    ; gasLimit := gas
    ; gasPrice := gasPrice
    ; accessList := accessList
    ; blobVersionedHashes := []
    ; maxFeePerBlobGas := NONE
    ; maxFeePerGas := NONE
  |>
End

val transaction1_from_rlp_pre_def = transaction1_from_rlp_def
  |> SRULE [GSYM OPT_MMAP_access_list_entry_from_rlp_eq]
  |> cv_auto_trans_pre;

Theorem transaction1_from_rlp_pre[cv_pre]:
  transaction1_from_rlp_pre x
Proof
  rw[transaction1_from_rlp_pre_def]
QED

Definition transaction2_from_rlp_def:
  transaction2_from_rlp baseFee rlp =
  if ¬is_RLPL rlp then NONE else
  let ls = dest_RLPL rlp in
  if LENGTH ls ≠ 12 then NONE else
  (* chain_id: U64 *)
  let nonce = EL 1 ls in
  if ¬is_RLPB nonce then NONE else
  let nonce = num_of_be_bytes $ dest_RLPB nonce in
  let maxPrio = EL 2 ls in
  if ¬is_RLPB maxPrio then NONE else
  let maxPrio = num_of_be_bytes $ dest_RLPB maxPrio in
  let maxFee = EL 3 ls in
  if ¬is_RLPB maxFee then NONE else
  let maxFee = num_of_be_bytes $ dest_RLPB maxFee in
  let gas = EL 4 ls in
  if ¬is_RLPB gas then NONE else
  let gas = num_of_be_bytes $ dest_RLPB gas in
  let to = EL 5 ls in
  if ¬is_RLPB to then NONE else
  let to = dest_RLPB to in
  let to = if LENGTH to = 0 then NONE
           else SOME $ word_of_bytes T 0w to in
  let value = EL 6 ls in
  if ¬is_RLPB value then NONE else
  let value = num_of_be_bytes $ dest_RLPB value in
  let data = EL 7 ls in
  if ¬is_RLPB data then NONE else
  let data = dest_RLPB data in
  let accessList = EL 8 ls in
  if ¬is_RLPL accessList then NONE else
  case OPT_MMAP access_list_entry_from_rlp (dest_RLPL accessList)
  of NONE => NONE |
  SOME accessList =>
  let yParity = EL 9 ls in
  let r = EL 10 ls in
  let s = EL 11 ls in
  SOME <|
      from := 0w (* TODO: ecrecover from yParity r s *)
    ; to := to
    ; data := data
    ; nonce := nonce
    ; value := value
    ; gasLimit := gas
    ; gasPrice := effective_gas_price baseFee maxFee maxPrio
    ; accessList := accessList
    ; blobVersionedHashes := []
    ; maxFeePerBlobGas := NONE
    ; maxFeePerGas := SOME maxFee
  |>
End

val transaction2_from_rlp_pre_def = transaction2_from_rlp_def
  |> SRULE [GSYM OPT_MMAP_access_list_entry_from_rlp_eq]
  |> cv_auto_trans_pre;

Theorem transaction2_from_rlp_pre[cv_pre]:
  transaction2_from_rlp_pre bf x
Proof
  rw[transaction2_from_rlp_pre_def]
QED

Definition transaction3_from_rlp_def:
  transaction3_from_rlp baseFee rlp =
  if ¬is_RLPL rlp then NONE else
  let ls = dest_RLPL rlp in
  if LENGTH ls ≠ 14 then NONE else
  (* chain_id: U64 *)
  let nonce = EL 1 ls in
  if ¬is_RLPB nonce then NONE else
  let nonce = num_of_be_bytes $ dest_RLPB nonce in
  let maxPrio = EL 2 ls in
  if ¬is_RLPB maxPrio then NONE else
  let maxPrio = num_of_be_bytes $ dest_RLPB maxPrio in
  let maxFee = EL 3 ls in
  if ¬is_RLPB maxFee then NONE else
  let maxFee = num_of_be_bytes $ dest_RLPB maxFee in
  let gas = EL 4 ls in
  if ¬is_RLPB gas then NONE else
  let gas = num_of_be_bytes $ dest_RLPB gas in
  let to = EL 5 ls in
  if ¬is_RLPB to then NONE else
  let to = dest_RLPB to in
  let to = if LENGTH to = 0 then NONE
           else SOME $ word_of_bytes T 0w to in
  let value = EL 6 ls in
  if ¬is_RLPB value then NONE else
  let value = num_of_be_bytes $ dest_RLPB value in
  let data = EL 7 ls in
  if ¬is_RLPB data then NONE else
  let data = dest_RLPB data in
  let accessList = EL 8 ls in
  if ¬is_RLPL accessList then NONE else
  case OPT_MMAP access_list_entry_from_rlp (dest_RLPL accessList)
  of NONE => NONE |
  SOME accessList =>
  let maxBlobFee = EL 9 ls in
  if ¬is_RLPB maxBlobFee then NONE else
  let maxBlobFee = num_of_be_bytes $ dest_RLPB maxBlobFee in
  let blobHashes = EL 10 ls in
  if ¬is_RLPL blobHashes then NONE else
  let blobHashes = dest_RLPL blobHashes in
  if ¬(EVERY is_RLPB blobHashes) then NONE else
  let blobHashes = MAP (word_of_bytes T 0w o dest_RLPB) blobHashes in
  let yParity = EL 11 ls in
  let r = EL 12 ls in
  let s = EL 13 ls in
  SOME <|
      from := 0w (* TODO: ecrecover from yParity r s *)
    ; to := to
    ; data := data
    ; nonce := nonce
    ; value := value
    ; gasLimit := gas
    ; gasPrice := effective_gas_price baseFee maxFee maxPrio
    ; accessList := accessList
    ; blobVersionedHashes := blobHashes
    ; maxFeePerBlobGas := SOME maxBlobFee
    ; maxFeePerGas := SOME maxFee
  |>
End

val transaction3_from_rlp_pre_def = transaction3_from_rlp_def
  |> SRULE [GSYM OPT_MMAP_access_list_entry_from_rlp_eq]
  |> cv_auto_trans_pre;

Theorem transaction3_from_rlp_pre[cv_pre]:
  transaction3_from_rlp_pre bf x
Proof
  rw[transaction3_from_rlp_pre_def]
QED

Definition transaction_from_rlp_def:
  transaction_from_rlp baseFee rlp =
  if is_RLPL rlp then
    let ls = dest_RLPL rlp in
    if ¬(LENGTH ls = 9 ∧ EVERY is_RLPB ls) then NONE else
    let nonce = EL 0 ls in
    let gasPrice = EL 1 ls in
    let gas = EL 2 ls in
    let to = dest_RLPB $ EL 3 ls in
    let value = EL 4 ls in
    let data = EL 5 ls in
    let v = EL 6 ls in
    let r = EL 7 ls in
    let s = EL 8 ls in
      SOME <|
        from := 0w (* TODO: ecrecover from v r s *)
      ; to := if LENGTH to = 0 then NONE
              else SOME $ word_of_bytes T 0w to
      ; data := dest_RLPB data
      ; nonce := num_of_be_bytes $ dest_RLPB nonce
      ; value := num_of_be_bytes $ dest_RLPB value
      ; gasLimit := num_of_be_bytes $ dest_RLPB gas
      ; gasPrice := num_of_be_bytes $ dest_RLPB gasPrice
      ; accessList := []
      ; blobVersionedHashes := []
      ; maxFeePerBlobGas := NONE
      ; maxFeePerGas := NONE
      |>
  else let bs = dest_RLPB rlp in
  if NULL bs then NONE else
  if HD bs = 1w then
    case rlp_decode (TL bs) of NONE => NONE |
    SOME rlp => transaction1_from_rlp rlp
  else if HD bs = 2w then
    case rlp_decode (TL bs) of NONE => NONE |
    SOME rlp => transaction2_from_rlp baseFee rlp
  else if HD bs = 3w then
    case rlp_decode (TL bs) of NONE => NONE |
    SOME rlp => transaction3_from_rlp baseFee rlp
  else NONE
End

val transaction_from_rlp_pre_def = cv_auto_trans_pre transaction_from_rlp_def;

Theorem transaction_from_rlp_pre[cv_pre]:
  transaction_from_rlp_pre bf x
Proof
  rw[transaction_from_rlp_pre_def]
  \\ strip_tac \\ gvs[]
QED

Definition OPT_MMAP_transaction_from_rlp_def:
  OPT_MMAP_transaction_from_rlp bf [] = SOME [] ∧
  OPT_MMAP_transaction_from_rlp bf (x::xs) =
  case transaction_from_rlp bf x of NONE => NONE
     | SOME h =>
         case OPT_MMAP_transaction_from_rlp bf xs of NONE => NONE
            | SOME t => SOME (h::t)
End

val () = cv_auto_trans OPT_MMAP_transaction_from_rlp_def;

Theorem OPT_MMAP_transaction_from_rlp_eq:
  OPT_MMAP_transaction_from_rlp bf ls =
  OPT_MMAP (transaction_from_rlp bf) ls
Proof
  Induct_on`ls` \\ rw[OPT_MMAP_transaction_from_rlp_def]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
QED

Definition OPT_MMAP_withdrawal_from_rlp_def:
  OPT_MMAP_withdrawal_from_rlp [] = SOME [] ∧
  OPT_MMAP_withdrawal_from_rlp (x::xs) =
  case withdrawal_from_rlp x of NONE => NONE
     | SOME h =>
         case OPT_MMAP_withdrawal_from_rlp xs of NONE => NONE
            | SOME t => SOME (h::t)
End

val () = cv_auto_trans OPT_MMAP_withdrawal_from_rlp_def;

Theorem OPT_MMAP_withdrawal_from_rlp_eq:
  OPT_MMAP_withdrawal_from_rlp ls =
  OPT_MMAP withdrawal_from_rlp ls
Proof
  Induct_on`ls` \\ rw[OPT_MMAP_withdrawal_from_rlp_def]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
QED

Definition block_from_rlp_def:
  block_from_rlp rlp =
  if ¬is_RLPL rlp then NONE else
  let ls = dest_RLPL rlp in
  if LENGTH ls ≠ 4 then NONE else
  let header = EL 0 ls in
  let transactions = EL 1 ls in
  let ommers = EL 2 ls in
  let withdrawals = EL 3 ls in
  case block_header_from_rlp header of NONE => NONE |
  SOME blk =>
  if ¬is_RLPL transactions then NONE else
  let ls = dest_RLPL transactions in
  case OPT_MMAP (transaction_from_rlp blk.baseFeePerGas) ls of NONE => NONE |
  SOME transactions =>
  if ¬is_RLPL withdrawals then NONE else
  let ls = dest_RLPL withdrawals in
  case OPT_MMAP withdrawal_from_rlp ls of NONE => NONE |
  SOME withdrawals =>
  SOME $
    blk with <|
      transactions := transactions
    ; withdrawals := withdrawals
    |>
End

val block_from_rlp_pre_def = block_from_rlp_def
  |> SRULE [GSYM OPT_MMAP_withdrawal_from_rlp_eq,
               GSYM OPT_MMAP_transaction_from_rlp_eq]
  |> cv_auto_trans_pre;

Theorem block_from_rlp_pre[cv_pre]:
  block_from_rlp_pre x
Proof
  rw[block_from_rlp_pre_def]
  \\ strip_tac \\ gvs[]
QED

(* -- *)

Definition run_test_def:
  run_test fuel
    preState
    genesisRLP
    genesisBlock
    validBlocks
    (validBlockRLPs: byte list list)
    lastBlockHash
    postState
    expectException
  =
    case rlp_decode genesisRLP
    of NONE => GenesisBlockDecodeFailure |
    SOME rlp =>
    case block_from_rlp rlp
    of NONE => GenesisBlockDecodeFailure |
    SOME decodedGenesisBlock =>
    if decodedGenesisBlock with hash := genesisBlock.hash <> genesisBlock
    then GenesisBlockDecodeMismatch
    else case state_root_clocked fuel preState
    of NONE => OutOfFuel |
    SOME preStateRootBytes =>
    let preStateRoot = word_of_bytes T 0w preStateRootBytes in
    if preStateRoot ≠ genesisBlock.stateRoot
    then GenesisHeaderMismatch preStateRoot
    else
      (* TODO: check validBlockRLPs decode to validBlocks *)
    case
      run_blocks (Collect empty_domain) 1 [] genesisBlock preState validBlocks
    of NONE => UnexpectedException
     | SOME (_, hashes, parent, computedPostState, dom) =>
    case expectException of NONE =>
      let computedHash = case hashes of h::_ => h | _ => genesisBlock.hash in
      if computedHash <> lastBlockHash then LastHashMismatch computedHash else
      if computedPostState <> postState then StateMismatch else Passed
    | SOME (msg, (rlp: word8 list), decoded) =>
        (* TODO: check rlp decodes to decoded *)
        case decoded of NONE => ExpectedException "block rlp decoding"
        | SOME invalidBlock =>
            case run_blocks dom 1 hashes parent computedPostState [invalidBlock] of
          NONE => Passed (* TODO: check exception match *)
        | SOME _ => ExpectedException msg
End

val () = cv_auto_trans run_test_def;

val () = export_theory();
