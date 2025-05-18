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

Definition block_header_from_block_rlp_def:
  block_header_from_block_rlp rlp =
  if ¬is_RLPL rlp then NONE else
  let ls = dest_RLPL rlp in
  if LENGTH ls ≠ 4 then NONE else
  let rlp = EL 0 ls in
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

val block_header_from_block_rlp_pre_def =
  cv_auto_trans_pre block_header_from_block_rlp_def;

Theorem block_header_from_block_rlp_pre[cv_pre]:
  block_header_from_block_rlp_pre x
Proof
  rw[block_header_from_block_rlp_pre_def]
  \\ Cases_on`x` \\ gvs[]
  \\ strip_tac \\ gvs[]
QED

Definition run_test_def:
  run_test fuel
    preState
    (genesisRLP: byte list)
    (genesisBlock: block)
    validBlocks
    lastBlockHash
    postState
    expectException
  =
    case rlp_decode genesisRLP
    of NONE => GenesisBlockDecodeFailure |
    SOME rlp =>
    case block_header_from_block_rlp rlp
    of NONE => GenesisBlockDecodeFailure |
    SOME genesisHeader =>
    if genesisHeader with hash := genesisBlock.hash <> genesisBlock
    then GenesisBlockDecodeMismatch
    else case state_root_clocked fuel preState
    of NONE => OutOfFuel |
    SOME preStateRootBytes =>
    let preStateRoot = word_of_bytes T 0w preStateRootBytes in
    if preStateRoot ≠ genesisBlock.stateRoot
    then GenesisHeaderMismatch preStateRoot
    else case
      (* TODO: check RLP decoding first *)
      run_blocks (Collect empty_domain) 1 [] genesisBlock preState validBlocks
    of NONE => UnexpectedException
     | SOME (_, hashes, parent, computedPostState, dom) =>
    case expectException of NONE =>
      let computedHash = case hashes of h::_ => h | _ => genesisBlock.hash in
      if computedHash <> lastBlockHash then LastHashMismatch computedHash else
      if computedPostState <> postState then StateMismatch else Passed
    | SOME (msg, (rlp: word8 list), decoded) =>
        (* TODO: check RLP *)
        case decoded of NONE => ExpectedException "block rlp decoding"
        | SOME invalidBlock =>
            case run_blocks dom 1 hashes parent computedPostState [invalidBlock] of
          NONE => Passed (* TODO: check exception match *)
        | SOME _ => ExpectedException msg
End

val () = cv_auto_trans run_test_def;

val () = export_theory();
