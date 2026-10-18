Theory vfmTestRun
Ancestors pair sorting byte sum words cv_type
  vfmTypes vfmExecution vfmState vfmContext
  vfmOperation vfmCompute vfmBlockDecode
Libs
  wordsLib permLib cv_transLib dep_rewrite

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

(* A fixture block with the RLP chunks it is given as. An invalid block may
   have no decoded form, when its RLP is not a valid block. *)
Datatype:
  test_block
  = ValidBlock block (byte list list)
  | InvalidBlock string (byte list list) (block option)
End

(* Runs the blocks in order from the chain state (dom, hashes, parent,
   state). A valid block must decode from its RLP and execute; an invalid
   block must be rejected, and leaves the chain state unchanged. At the end
   the head block and state must match lastBlockHash and postState. *)
Definition run_test_blocks_def:
  run_test_blocks lastBlockHash postState dom hashes parent state [] =
    (if parent.hash <> lastBlockHash then LastHashMismatch parent.hash else
     if state <> postState then StateMismatch else Passed) ∧
  run_test_blocks lastBlockHash postState dom hashes parent state
    (ValidBlock blk rlpbs :: blocks) =
    (case OPTION_BIND (rlp_decode_chunks rlpbs) block_from_rlp
     of NONE => BlockDecodeFailure
      | SOME decoded =>
        if decoded with hash := blk.hash <> blk then BlockDecodeMismatch else
        case run_block dom 1 hashes parent state blk
        of NONE => UnexpectedException
         | SOME (_, state', dom') =>
           run_test_blocks lastBlockHash postState
             dom' (blk.hash::hashes) blk state' blocks) ∧
  run_test_blocks lastBlockHash postState dom hashes parent state
    (InvalidBlock msg rlpbs optblock :: blocks) =
    case OPTION_BIND (rlp_decode_chunks rlpbs) block_from_rlp
    of NONE => (* TODO: check exception msg *)
       run_test_blocks lastBlockHash postState dom hashes parent state blocks
     | SOME decoded =>
       (* fixtures omit rlp_decoded only for RLP_STRUCTURES_ENCODING, which
          the decoder should have rejected *)
       case optblock of NONE => ExpectedException "block rlp decoding"
       | SOME invalidBlock =>
         if decoded with hash := invalidBlock.hash <> invalidBlock
         then BlockDecodeMismatch else
         case run_block dom 1 hashes parent state invalidBlock
         of NONE => (* TODO: check exception msg *)
            run_test_blocks lastBlockHash postState dom hashes parent state
              blocks
          | SOME _ => ExpectedException msg
End

val run_test_blocks_pre_def =
  cv_auto_trans_pre "run_test_blocks_pre" run_test_blocks_def;

Theorem run_test_blocks_pre[cv_pre]:
  ∀lastBlockHash postState dom hashes parent state blocks.
    run_test_blocks_pre lastBlockHash postState dom hashes parent state blocks
Proof
  ho_match_mp_tac run_test_blocks_ind
  \\ rw[]
  \\ rw[Once run_test_blocks_pre_def]
  \\ gvs[]
  \\ rename1 `block_from_rlp _ = SOME decoded`
  \\ Cases_on `decoded`
  \\ gvs[block_component_equality]
QED

Definition run_test_def:
  run_test
    preState
    genesisRLP
    genesisBlock
    blocks
    lastBlockHash
    postState
  =
    case rlp_decode_chunks genesisRLP
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
    else run_test_blocks lastBlockHash postState
           (Collect empty_domain) [genesisBlock.hash] genesisBlock preState
           blocks
End

val () = cv_auto_trans $
  REWRITE_RULE[GSYM word_of_bytes_be_def] run_test_def;
