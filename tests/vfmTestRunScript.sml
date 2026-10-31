Theory vfmTestRun
Ancestors pair sorting byte sum words cv_type cv_std
  vfmTypes vfmExecution vfmState vfmContext
  vfmOperation vfmCompute vfmBlockDecode vfmRoot
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

(* The chain the conformance fixtures are signed for. *)
Definition test_chain_id_def:
  test_chain_id = 1n
End

val () = cv_auto_trans test_chain_id_def;

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
    (case OPTION_BIND (rlp_decode_chunks rlpbs) (block_from_rlp test_chain_id)
     of NONE => BlockDecodeFailure
      | SOME decoded =>
        if decoded with hash := blk.hash <> blk then BlockDecodeMismatch else
        case run_block dom test_chain_id hashes parent state blk
        of NONE => UnexpectedException
         | SOME (_, state', dom') =>
           run_test_blocks lastBlockHash postState
             dom' (blk.hash::hashes) blk state' blocks) ∧
  run_test_blocks lastBlockHash postState dom hashes parent state
    (InvalidBlock msg rlpbs optblock :: blocks) =
    case OPTION_BIND (rlp_decode_chunks rlpbs) (block_from_rlp test_chain_id)
    of NONE => (* TODO: check exception msg *)
       run_test_blocks lastBlockHash postState dom hashes parent state blocks
     | SOME decoded =>
       (* fixtures omit rlp_decoded only for RLP_STRUCTURES_ENCODING, which
          the decoder should have rejected *)
       case optblock of NONE => ExpectedException "block rlp decoding"
       | SOME invalidBlock =>
         if decoded with hash := invalidBlock.hash <> invalidBlock
         then BlockDecodeMismatch else
         case run_block dom test_chain_id hashes parent state invalidBlock
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
  \\ rename1 `block_from_rlp _ _ = SOME decoded`
  \\ Cases_on `decoded`
  \\ gvs[block_component_equality]
QED

(* run_test with the genesis state root supplied by the caller, so a root
   proved once can be shared by every test with the same pre-state. *)
Definition run_test_with_root_def:
  run_test_with_root
    preStateRootBytes
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
    case block_from_rlp test_chain_id rlp
    of NONE => GenesisBlockDecodeFailure |
    SOME decodedGenesisBlock =>
    if decodedGenesisBlock with hash := genesisBlock.hash <> genesisBlock
    then GenesisBlockDecodeMismatch
    else let preStateRoot = word_of_bytes T 0w preStateRootBytes in
    if preStateRoot ≠ genesisBlock.stateRoot
    then GenesisHeaderMismatch preStateRoot
    else run_test_blocks lastBlockHash postState
           (Collect empty_domain) [genesisBlock.hash] genesisBlock preState
           blocks
End

val () = cv_auto_trans $
  REWRITE_RULE[GSYM word_of_bytes_be_def] run_test_with_root_def;

Definition run_test_def:
  run_test
    preState
    genesisRLP
    genesisBlock
    blocks
    lastBlockHash
    postState
  =
    run_test_with_root (state_root preState)
      preState genesisRLP genesisBlock blocks lastBlockHash postState
End

val () = cv_auto_trans run_test_def;

(* state_root with storage roots and code hashes looked up in tables of
   already-proved values. Each table entry only has to be correct, not
   complete: a missing entry falls back to computing the value. *)

Definition storage_root_memo_def:
  storage_root_memo [] s = storage_root s ∧
  storage_root_memo ((k,r)::t) s =
    if k = s then (r:word8 list) else storage_root_memo t s
End

val () = cv_auto_trans storage_root_memo_def;

Definition code_hash_memo_def:
  code_hash_memo [] c = Keccak_256_w64 c ∧
  code_hash_memo ((k,h)::t) c =
    if k = c then (h:word8 list) else code_hash_memo t c
End

val () = cv_auto_trans code_hash_memo_def;

Theorem storage_root_memo_thm:
  EVERY (λ(k,r). storage_root k = r) t ⇒
  storage_root_memo t s = storage_root s
Proof
  Induct_on`t` \\ simp[FORALL_PROD, storage_root_memo_def]
  \\ rw[] \\ gvs[]
QED

Theorem code_hash_memo_thm:
  EVERY (λ(k,h). Keccak_256_w64 k = h) t ⇒
  code_hash_memo t c = Keccak_256_w64 c
Proof
  Induct_on`t` \\ simp[FORALL_PROD, code_hash_memo_def]
  \\ rw[] \\ gvs[]
QED

Definition encode_account_memo_def:
  encode_account_memo st ct a = rlp_encode $ RLPL [
    rlp_number a.nonce;
    rlp_number a.balance;
    RLPB $ storage_root_memo st a.storage;
    RLPB $ code_hash_memo ct a.code
  ]
End

Definition state_kvs_memo_def:
  state_kvs_memo st ct [] acc = REVERSE acc ∧
  state_kvs_memo st ct ((k,v)::ls) acc =
  state_kvs_memo st ct ls
    ((account_key $ n2w k, encode_account_memo st ct v)::acc)
End

val () = cv_auto_trans state_kvs_memo_def;

Definition state_root_memo_def:
  state_root_memo st ct (a: evm_accounts) =
  trie_root_from_kvs $ state_kvs_memo st ct
    (toAList (build_spt empty_account_state (dimword (:160)) a)) []
End

Definition cv_state_root_memo_def:
  cv_state_root_memo st ct (a:cv) =
  cv_trie_root_from_kvs $
    cv_state_kvs_memo st ct (cv_toAList a) (cv$Num 0)
End

Theorem cv_state_root_memo_rep[cv_rep]:
  from_list from_word $ state_root_memo st ct a =
  cv_state_root_memo
    (from_list (from_pair from_storage (from_list from_word)) st)
    (from_list (from_pair (from_list from_word) (from_list from_word)) ct)
    (from_evm_accounts a)
Proof
  simp[cv_state_root_memo_def, state_root_memo_def,
       from_evm_accounts_def, Excl"SIZES_CONV",
       vfmRootTheory.cv_trie_root_from_kvs_thm]
  \\ qmatch_goalsub_abbrev_tac`from_sptree_sptree_spt _ t`
  \\ simp[GSYM cv_toAList_thm]
  \\ simp[theorem"cv_state_kvs_memo_thm" |> GSYM |> Q.GEN`acc`
          |> Q.SPEC`[]` |> SIMP_RULE std_ss [from_list_def]]
QED

Theorem state_root_memo_thm:
  EVERY (λ(k,r). storage_root k = r) st ∧
  EVERY (λ(k,h). Keccak_256_w64 k = h) ct ⇒
  ∀a. state_root_memo st ct a = state_root a
Proof
  rpt strip_tac
  \\ `∀ls acc. state_kvs_memo st ct ls acc = state_kvs ls acc`
  by (
    Induct \\ simp[FORALL_PROD, state_kvs_memo_def, state_kvs_def]
    \\ simp[encode_account_memo_def, encode_account_def,
            storage_root_memo_thm, code_hash_memo_thm] )
  \\ simp[state_root_memo_def, state_root_eqn]
QED
