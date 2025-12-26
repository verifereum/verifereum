open HolKernel boolLib bossLib Parse wordsLib dep_rewrite permLib
     pairTheory sortingTheory sumTheory wordsTheory
     vfmTypesTheory vfmExecutionTheory
     vfmStateTheory vfmContextTheory
     vfmOperationTheory vfmComputeTheory
     cv_transLib cv_typeTheory

val () = new_theory "vfmTestRun";

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
End

Definition isPassed_def:
  (isPassed Passed ⇔ T) ∧
  (isPassed _ ⇔ F)
End

(* TODO: move to another theory? *)

Definition block_header_from_rlp_def:
  block_header_from_rlp rlp =
  if ¬is_RLPL rlp then NONE else
  let ls = dest_RLPL rlp in
  if ¬(LENGTH ls = 21 ∧ EVERY is_RLPB ls) then NONE else
  let coinbase   = dest_RLPB (EL  2 ls) in
  let stateRoot  = dest_RLPB (EL  3 ls) in
  let number     = dest_RLPB (EL  8 ls) in
  let gasLimit   = dest_RLPB (EL  9 ls) in
  let gasUsed    = dest_RLPB (EL 10 ls) in
  let timestamp  = dest_RLPB (EL 11 ls) in
  let prevRandao = dest_RLPB (EL 13 ls) in
  let baseFeePerGas = dest_RLPB (EL 15 ls) in
  let withdrawalsRoot = dest_RLPB (EL 16 ls) in
  let blobGasUsed   = dest_RLPB (EL 17 ls) in
  let excessBlobGas = dest_RLPB (EL 18 ls) in
  let parentBeaconBlockRoot = dest_RLPB (EL 19 ls) in
  let requestsHash = dest_RLPB (EL 20 ls) in
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
     parentBeaconBlockRoot;
     requestsHash
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
     ; requestsHash  := word_of_bytes T 0w requestsHash
     ; stateRoot     := word_of_bytes T 0w stateRoot
     ; withdrawalsRoot := word_of_bytes T 0w withdrawalsRoot
     (* not in header *)
     ; hash          := 0w
     ; transactions  := []
     ; withdrawals   := []
     |>
End

val block_header_from_rlp_pre_def =
  cv_auto_trans_pre "block_header_from_rlp_pre" block_header_from_rlp_def;

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

val withdrawal_from_rlp_pre_def = cv_auto_trans_pre "withdrawal_from_rlp_pre" withdrawal_from_rlp_def;

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
  cv_auto_trans_pre "access_list_entry_from_rlp_pre" access_list_entry_from_rlp_def;

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
  let nonceRlp = EL 1 ls in
  if ¬is_RLPB nonceRlp then NONE else
  let nonce = num_of_be_bytes $ dest_RLPB nonceRlp in
  let gasPriceRlp = EL 2 ls in
  if ¬is_RLPB gasPriceRlp then NONE else
  let gasPrice = num_of_be_bytes $ dest_RLPB gasPriceRlp in
  let gasRlp = EL 3 ls in
  if ¬is_RLPB gasRlp then NONE else
  let gas = num_of_be_bytes $ dest_RLPB gasRlp in
  let toRlp = EL 4 ls in
  if ¬is_RLPB toRlp then NONE else
  let to = dest_RLPB toRlp in
  let to = if LENGTH to = 0 then NONE
           else SOME $ word_of_bytes T 0w to in
  let valueRlp = EL 5 ls in
  if ¬is_RLPB valueRlp then NONE else
  let value = num_of_be_bytes $ dest_RLPB valueRlp in
  let dataRlp = EL 6 ls in
  if ¬is_RLPB dataRlp then NONE else
  let data = dest_RLPB dataRlp in
  let accessListRlp = EL 7 ls in
  if ¬is_RLPL accessListRlp then NONE else
  case OPT_MMAP access_list_entry_from_rlp (dest_RLPL accessListRlp)
  of NONE => NONE |
  SOME accessList =>
  let yParity = EL 8 ls in
  if ¬is_RLPB yParity then NONE else
  let yParity = num_of_be_bytes $ dest_RLPB yParity in
  let r = EL 9 ls in
  if ¬is_RLPB r then NONE else
  let r = num_of_be_bytes $ dest_RLPB r in
  let s = EL 10 ls in
  if ¬is_RLPB s then NONE else
  let s = num_of_be_bytes $ dest_RLPB s in
  let txLs = [
    rlp_number 1; nonceRlp; gasPriceRlp; gasRlp; toRlp;
    valueRlp; dataRlp; accessListRlp ] in
  let hash = word_of_bytes T 0w $ Keccak_256_w64 $
    1w :: rlp_encode (RLPL txLs) in
  case ecrecover hash (yParity + 27) r s of NONE => NONE |
  SOME addr =>
  SOME <|
      from := addr
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
    ; authorizationList := []
  |>
End

val transaction1_from_rlp_pre_def = transaction1_from_rlp_def
  |> SRULE [GSYM OPT_MMAP_access_list_entry_from_rlp_eq]
  |> cv_auto_trans_pre "transaction1_from_rlp_pre";

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
  let nonceRlp = EL 1 ls in
  if ¬is_RLPB nonceRlp then NONE else
  let nonce = num_of_be_bytes $ dest_RLPB nonceRlp in
  let maxPrioRlp = EL 2 ls in
  if ¬is_RLPB maxPrioRlp then NONE else
  let maxPrio = num_of_be_bytes $ dest_RLPB maxPrioRlp in
  let maxFeeRlp = EL 3 ls in
  if ¬is_RLPB maxFeeRlp then NONE else
  let maxFee = num_of_be_bytes $ dest_RLPB maxFeeRlp in
  let gasRlp = EL 4 ls in
  if ¬is_RLPB gasRlp then NONE else
  let gas = num_of_be_bytes $ dest_RLPB gasRlp in
  let toRlp = EL 5 ls in
  if ¬is_RLPB toRlp then NONE else
  let to = dest_RLPB toRlp in
  let to = if LENGTH to = 0 then NONE
           else SOME $ word_of_bytes T 0w to in
  let valueRlp = EL 6 ls in
  if ¬is_RLPB valueRlp then NONE else
  let value = num_of_be_bytes $ dest_RLPB valueRlp in
  let dataRlp = EL 7 ls in
  if ¬is_RLPB dataRlp then NONE else
  let data = dest_RLPB dataRlp in
  let accessListRlp = EL 8 ls in
  if ¬is_RLPL accessListRlp then NONE else
  case OPT_MMAP access_list_entry_from_rlp (dest_RLPL accessListRlp)
  of NONE => NONE |
  SOME accessList =>
  let yParity = EL 9 ls in
  if ¬is_RLPB yParity then NONE else
  let yParity = num_of_be_bytes $ dest_RLPB yParity in
  let r = EL 10 ls in
  if ¬is_RLPB r then NONE else
  let r = num_of_be_bytes $ dest_RLPB r in
  let s = EL 11 ls in
  if ¬is_RLPB s then NONE else
  let s = num_of_be_bytes $ dest_RLPB s in
  let txLs = [
    rlp_number 1; nonceRlp; maxPrioRlp; maxFeeRlp; gasRlp;
    toRlp; valueRlp; dataRlp; accessListRlp ] in
  let hash = word_of_bytes T 0w $ Keccak_256_w64 $
    2w :: rlp_encode (RLPL txLs) in
  case ecrecover hash (yParity + 27) r s of NONE => NONE |
  SOME addr =>
  SOME <|
      from := addr
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
    ; authorizationList := []
  |>
End

val transaction2_from_rlp_pre_def = transaction2_from_rlp_def
  |> SRULE [GSYM OPT_MMAP_access_list_entry_from_rlp_eq]
  |> cv_auto_trans_pre "transaction2_from_rlp_pre";

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
  let nonceRlp = EL 1 ls in
  if ¬is_RLPB nonceRlp then NONE else
  let nonce = num_of_be_bytes $ dest_RLPB nonceRlp in
  let maxPrioRlp = EL 2 ls in
  if ¬is_RLPB maxPrioRlp then NONE else
  let maxPrio = num_of_be_bytes $ dest_RLPB maxPrioRlp in
  let maxFeeRlp = EL 3 ls in
  if ¬is_RLPB maxFeeRlp then NONE else
  let maxFee = num_of_be_bytes $ dest_RLPB maxFeeRlp in
  let gasRlp = EL 4 ls in
  if ¬is_RLPB gasRlp then NONE else
  let gas = num_of_be_bytes $ dest_RLPB gasRlp in
  let toRlp = EL 5 ls in
  if ¬is_RLPB toRlp then NONE else
  let to = dest_RLPB toRlp in
  let to = if LENGTH to = 0 then NONE
           else SOME $ word_of_bytes T 0w to in
  let valueRlp = EL 6 ls in
  if ¬is_RLPB valueRlp then NONE else
  let value = num_of_be_bytes $ dest_RLPB valueRlp in
  let dataRlp = EL 7 ls in
  if ¬is_RLPB dataRlp then NONE else
  let data = dest_RLPB dataRlp in
  let accessListRlp = EL 8 ls in
  if ¬is_RLPL accessListRlp then NONE else
  case OPT_MMAP access_list_entry_from_rlp (dest_RLPL accessListRlp)
  of NONE => NONE |
  SOME accessList =>
  let maxBlobFeeRlp = EL 9 ls in
  if ¬is_RLPB maxBlobFeeRlp then NONE else
  let maxBlobFee = num_of_be_bytes $ dest_RLPB maxBlobFeeRlp in
  let blobHashesRlp = EL 10 ls in
  if ¬is_RLPL blobHashesRlp then NONE else
  let blobHashes = dest_RLPL blobHashesRlp in
  if IS_NONE to /\ ~(NULL blobHashes) then NONE else
  if ¬(EVERY is_RLPB blobHashes) then NONE else
  let blobHashes = MAP (word_of_bytes T 0w o dest_RLPB) blobHashes in
  let yParity = EL 11 ls in
  if ¬is_RLPB yParity then NONE else
  let yParity = num_of_be_bytes $ dest_RLPB yParity in
  let r = EL 12 ls in
  if ¬is_RLPB r then NONE else
  let r = num_of_be_bytes $ dest_RLPB r in
  let s = EL 13 ls in
  if ¬is_RLPB s then NONE else
  let s = num_of_be_bytes $ dest_RLPB s in
  let txLs = [
    rlp_number 1; nonceRlp; maxPrioRlp; maxFeeRlp; gasRlp;
    toRlp; valueRlp; dataRlp; accessListRlp; maxBlobFeeRlp; blobHashesRlp ] in
  let hash = word_of_bytes T 0w $ Keccak_256_w64 $
    3w :: rlp_encode (RLPL txLs) in
  case ecrecover hash (yParity + 27) r s of NONE => NONE |
  SOME addr =>
  SOME <|
      from := addr
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
    ; authorizationList := []
  |>
End

val transaction3_from_rlp_pre_def = transaction3_from_rlp_def
  |> SRULE [GSYM OPT_MMAP_access_list_entry_from_rlp_eq]
  |> cv_auto_trans_pre "transaction3_from_rlp_pre";

Theorem transaction3_from_rlp_pre[cv_pre]:
  transaction3_from_rlp_pre bf x
Proof
  rw[transaction3_from_rlp_pre_def]
QED

Definition authorization_from_rlp_def:
  authorization_from_rlp rlp =
  if ¬is_RLPL rlp then NONE else
  let ls = dest_RLPL rlp in
  if LENGTH ls ≠ 6 then NONE else
  if ¬(EVERY is_RLPB ls) then NONE else
  let chainIdRlp = EL 0 ls in
  let chainId = num_of_be_bytes $ dest_RLPB chainIdRlp in
  let addressRlp = EL 1 ls in
  let address : address = word_of_bytes T 0w $ dest_RLPB addressRlp in
  let nonceRlp = EL 2 ls in
  let nonce = num_of_be_bytes $ dest_RLPB nonceRlp in
  let yParity = num_of_be_bytes $ dest_RLPB $ EL 3 ls in
  let r = num_of_be_bytes $ dest_RLPB $ EL 4 ls in
  let s = num_of_be_bytes $ dest_RLPB $ EL 5 ls in
  let authLs = [chainIdRlp; addressRlp; nonceRlp] in
  let hash = word_of_bytes T 0w $ Keccak_256_w64 $
    5w :: rlp_encode (RLPL authLs) in
  let authority = case ecrecover hash (yParity + 27) r s of
                    NONE => 0w | SOME a => a in
  SOME <| authority := authority
        ; delegate := address
        ; authChainId := chainId
        ; authNonce := nonce
        ; authS := s
        |>
End

val authorization_from_rlp_pre_def =
  cv_auto_trans_pre "authorization_from_rlp_pre" authorization_from_rlp_def;

Theorem authorization_from_rlp_pre[cv_pre]:
  authorization_from_rlp_pre x
Proof
  rw[authorization_from_rlp_pre_def]
  \\ strip_tac \\ gvs[]
QED

Definition OPT_MMAP_authorization_from_rlp_def:
  OPT_MMAP_authorization_from_rlp [] = SOME [] ∧
  OPT_MMAP_authorization_from_rlp (x::xs) =
  case authorization_from_rlp x of NONE => NONE
     | SOME h =>
         case OPT_MMAP_authorization_from_rlp xs of NONE => NONE
            | SOME t => SOME (h::t)
End

val () = cv_auto_trans OPT_MMAP_authorization_from_rlp_def;

Theorem OPT_MMAP_authorization_from_rlp_eq:
  OPT_MMAP_authorization_from_rlp ls =
  OPT_MMAP authorization_from_rlp ls
Proof
  Induct_on`ls` \\ rw[OPT_MMAP_authorization_from_rlp_def]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
QED

Definition transaction4_from_rlp_def:
  transaction4_from_rlp baseFee rlp =
  if ¬is_RLPL rlp then NONE else
  let ls = dest_RLPL rlp in
  if LENGTH ls ≠ 13 then NONE else
  (* chain_id: U64 *)
  let nonceRlp = EL 1 ls in
  if ¬is_RLPB nonceRlp then NONE else
  let nonce = num_of_be_bytes $ dest_RLPB nonceRlp in
  let maxPrioRlp = EL 2 ls in
  if ¬is_RLPB maxPrioRlp then NONE else
  let maxPrio = num_of_be_bytes $ dest_RLPB maxPrioRlp in
  let maxFeeRlp = EL 3 ls in
  if ¬is_RLPB maxFeeRlp then NONE else
  let maxFee = num_of_be_bytes $ dest_RLPB maxFeeRlp in
  let gasRlp = EL 4 ls in
  if ¬is_RLPB gasRlp then NONE else
  let gas = num_of_be_bytes $ dest_RLPB gasRlp in
  let toRlp = EL 5 ls in
  if ¬is_RLPB toRlp then NONE else
  let to = dest_RLPB toRlp in
  (* destination cannot be null in type 4 *)
  if LENGTH to = 0 then NONE else
  let to = SOME $ word_of_bytes T 0w to in
  let valueRlp = EL 6 ls in
  if ¬is_RLPB valueRlp then NONE else
  let value = num_of_be_bytes $ dest_RLPB valueRlp in
  let dataRlp = EL 7 ls in
  if ¬is_RLPB dataRlp then NONE else
  let data = dest_RLPB dataRlp in
  let accessListRlp = EL 8 ls in
  if ¬is_RLPL accessListRlp then NONE else
  case OPT_MMAP access_list_entry_from_rlp (dest_RLPL accessListRlp)
  of NONE => NONE |
  SOME accessList =>
  let authListRlp = EL 9 ls in
  if ¬is_RLPL authListRlp then NONE else
  (* authorization_list cannot be empty *)
  if NULL (dest_RLPL authListRlp) then NONE else
  case OPT_MMAP authorization_from_rlp (dest_RLPL authListRlp)
  of NONE => NONE |
  SOME authList =>
  let yParity = EL 10 ls in
  if ¬is_RLPB yParity then NONE else
  let yParity = num_of_be_bytes $ dest_RLPB yParity in
  let r = EL 11 ls in
  if ¬is_RLPB r then NONE else
  let r = num_of_be_bytes $ dest_RLPB r in
  let s = EL 12 ls in
  if ¬is_RLPB s then NONE else
  let s = num_of_be_bytes $ dest_RLPB s in
  let txLs = [
    rlp_number 1; nonceRlp; maxPrioRlp; maxFeeRlp; gasRlp;
    toRlp; valueRlp; dataRlp; accessListRlp; authListRlp ] in
  let hash = word_of_bytes T 0w $ Keccak_256_w64 $
    4w :: rlp_encode (RLPL txLs) in
  case ecrecover hash (yParity + 27) r s of NONE => NONE |
  SOME addr =>
  SOME <|
      from := addr
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
    ; authorizationList := authList
  |>
End

val transaction4_from_rlp_pre_def = transaction4_from_rlp_def
  |> SRULE [GSYM OPT_MMAP_access_list_entry_from_rlp_eq,
            GSYM OPT_MMAP_authorization_from_rlp_eq]
  |> cv_auto_trans_pre "transaction4_from_rlp_pre";

Theorem transaction4_from_rlp_pre[cv_pre]:
  transaction4_from_rlp_pre bf x
Proof
  rw[transaction4_from_rlp_pre_def]
QED

Definition transaction_from_rlp_def:
  transaction_from_rlp baseFee rlp =
  if is_RLPL rlp then
    let ls = dest_RLPL rlp in
    if ¬(LENGTH ls = 9 ∧ EVERY is_RLPB ls) then NONE else
    let nonce = EL 0 ls in
    let gasPrice = EL 1 ls in
    let gas = EL 2 ls in
    let toRlp = EL 3 ls in
    let to = dest_RLPB $ toRlp in
    let value = EL 4 ls in
    let data = EL 5 ls in
    let v = num_of_be_bytes $ dest_RLPB $ EL 6 ls in
    let r = num_of_be_bytes $ dest_RLPB $ EL 7 ls in
    let s = num_of_be_bytes $ dest_RLPB $ EL 8 ls in
    let txLs = [nonce; gasPrice; gas; toRlp; value; data] in
    let (txLs, v) = if v = 27 ∨ v = 28 then (txLs, v)
                    else (txLs ++ (MAP rlp_number [1; 0; 0]), v - 10) in
    let hash = word_of_bytes T 0w $ Keccak_256_w64 $ rlp_encode $ RLPL txLs in
    case ecrecover hash v r s of NONE => NONE |
      SOME addr =>
      SOME <|
        from := addr
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
      ; authorizationList := []
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
  else if HD bs = 4w then
    case rlp_decode (TL bs) of NONE => NONE |
    SOME rlp => transaction4_from_rlp baseFee rlp
  else NONE
End

val transaction_from_rlp_pre_def = cv_auto_trans_pre "transaction_from_rlp_pre" transaction_from_rlp_def;

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
  |> cv_auto_trans_pre "block_from_rlp_pre";

Theorem block_from_rlp_pre[cv_pre]:
  block_from_rlp_pre x
Proof
  rw[block_from_rlp_pre_def]
  \\ strip_tac \\ gvs[]
QED

(* -- *)

Definition check_block_rlps_def:
  check_block_rlps [] [] = Passed ∧
  check_block_rlps (bs::bss) (blk::blks) = (
  case OPTION_BIND (rlp_decode bs) block_from_rlp
    of NONE => BlockDecodeFailure
     | SOME dcd => if dcd with hash := blk.hash <> blk
                   then BlockDecodeMismatch
                   else check_block_rlps bss blks ) ∧
  check_block_rlps _ _ = BlockDecodeMismatch
End

val check_block_rlps_pre_def = cv_auto_trans_pre "check_block_rlps_pre" check_block_rlps_def;

Theorem check_block_rlps_pre[cv_pre]:
  ∀x y. check_block_rlps_pre x y
Proof
  ho_match_mp_tac check_block_rlps_ind
  \\ rw[]
  \\ rw[Once check_block_rlps_pre_def]
  \\ gvs[]
  \\ pop_assum mp_tac
  \\ CASE_TAC
  \\ strip_tac
  \\ gvs[block_component_equality]
QED

Definition run_test_def:
  run_test
    preState
    genesisRLP
    genesisBlock
    validBlocks
    validBlockRLPs
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
    else let preStateRootBytes = state_root preState in
    let preStateRoot = word_of_bytes T 0w preStateRootBytes in
    if preStateRoot ≠ genesisBlock.stateRoot
    then GenesisHeaderMismatch preStateRoot
    else
    let check = check_block_rlps validBlockRLPs validBlocks in
    if ¬isPassed check then check else
    case
      run_blocks (Collect empty_domain) 1
        [genesisBlock.hash] genesisBlock preState validBlocks
    of NONE => UnexpectedException
     | SOME (_, hashes, parent, computedPostState, dom) =>
    case expectException of NONE =>
      let computedHash = case hashes of h::_ => h | _ => genesisBlock.hash in
      if computedHash <> lastBlockHash then LastHashMismatch computedHash else
      if computedPostState <> postState then StateMismatch else Passed
    | SOME (msg, rlpbs, optblock) =>
        case OPTION_BIND (rlp_decode rlpbs) block_from_rlp of NONE =>
          Passed (* TODO: check exception msg *)
        | SOME decoded =>
        case optblock of NONE => ExpectedException "block rlp decoding"
        | SOME invalidBlock =>
          if decoded with hash := invalidBlock.hash <> invalidBlock
          then BlockDecodeMismatch else
          case run_blocks dom 1 hashes parent computedPostState [invalidBlock] of
          NONE => Passed (* TODO: check exception msg *)
        | SOME _ => ExpectedException msg
End

val () = cv_auto_trans run_test_def;

val () = export_theory();
