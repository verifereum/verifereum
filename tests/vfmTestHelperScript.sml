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
  | GenesisHeaderMismatch bytes32
  | GenesisStateMismatch bytes32
  | ExpectedException string
  | ExceptionMismatch
  | UnexpectedException
  | BlockDecodeFailure
  | LastHashMismatch bytes32
  | StateMismatch
  | OutOfFuel
End

Definition run_test_def:
  run_test fuel
    preState
    (genesisRLP: byte list) (* TODO: check RLP decoding *)
    (genesisBlock: block)
    validBlocks
    lastBlockHash
    postState
    expectException
  =
    case state_root_clocked fuel preState
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
