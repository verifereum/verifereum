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

Definition isPassed_def:
  (isPassed Passed ⇔ T) ∧
  (isPassed _ ⇔ F)
End

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

val () = cv_auto_trans $
  REWRITE_RULE[GSYM word_of_bytes_be_def] run_test_def;
