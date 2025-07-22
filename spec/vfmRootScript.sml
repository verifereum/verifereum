open HolKernel boolLib bossLib Parse wordsLib
     pairTheory combinTheory listTheory alistTheory wordsTheory
     sortingTheory sptreeTheory finite_mapTheory
     merklePatriciaTrieTheory vfmStateTheory
     cv_transLib cv_typeLib cv_typeTheory cv_stdTheory

val _ = new_theory "vfmRoot";

Definition storage_fmap_def:
  storage_fmap (s: storage) : bytes32 |-> bytes32 =
    build_fmap 0w (dimword (:256)) s
End

Theorem storage_fmap_empty_storage:
  storage_fmap empty_storage = FEMPTY
Proof
  rw[storage_fmap_def]
  \\ irule build_fmap_empty
  \\ rw[empty_storage_def]
QED

Theorem storage_fmap_update_storage:
  storage_fmap (update_storage k v s) =
  if v ≠ 0w then
    FUPDATE (storage_fmap s) (k, v)
  else
    (storage_fmap s) \\ k
Proof
  simp[storage_fmap_def, fmap_eq_flookup]
  \\ qx_gen_tac`x`
  \\ qspec_then`x`assume_tac w2n_lt
  \\ Cases_on`v = 0w`
  \\ simp[DOMSUB_FLOOKUP_THM, FLOOKUP_UPDATE]
  \\ gs[lookup_build_fmap, update_storage_def, APPLY_UPDATE_THM]
  \\ rw[] \\ gs[]
QED

Definition storage_key_def:
  storage_key k : word8 list =
  bytes_to_nibble_list $ Keccak_256_w64 $
  PAD_LEFT 0w 32 $ num_to_be_bytes k
End

val () = cv_auto_trans storage_key_def;

Definition storage_value_def:
  storage_value v : word8 list =
  rlp_encode $ rlp_number v
End

val () = cv_auto_trans storage_value_def;

Definition expanded_storage_trie_def:
  expanded_storage_trie s = let
    m = storage_fmap s;
    l = fmap_to_alist m;
    kvs = MAP (λ(k,v). (storage_key (w2n k), storage_value (w2n v))) l
  in patricialise kvs
End

Definition storage_trie_def:
  storage_trie s = OPTION_MAP encode_trie_node $ expanded_storage_trie s
End

Definition storage_root_def:
  storage_root s = trie_root $ storage_trie s
End

val from_to_storage_spt = from_to_thm_for “:bytes32 num_map”;

Theorem PERM_alist_build_fmap_build_spt:
  n ≤ dimword(:α) ⇒
  PERM
    (MAP (n2w ## I) (toAList (build_spt z n (s: α word -> β))))
    ((fmap_to_alist (build_fmap z n (s: α word -> β))) : (α word # β) list)
Proof
  strip_tac
  \\ irule PERM_ALL_DISTINCT
  \\ conj_tac
  >- (
    simp[MEM_fmap_to_alist_FLOOKUP, MEM_toAList, MEM_MAP,
         PULL_EXISTS, EXISTS_PROD, FORALL_PROD]
    \\ Cases
    \\ simp[lookup_build_fmap, lookup_build_spt]
    \\ rw[EQ_IMP_THM] \\ gs[]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[] )
  \\ conj_tac
  >- (
    irule ALL_DISTINCT_MAP_INJ
    \\ simp[FORALL_PROD, MEM_toAList, lookup_build_spt]
    \\ conj_tac
    >- ( rw[] \\ gs[] )
    \\ metis_tac[ALL_DISTINCT_MAP, ALL_DISTINCT_MAP_FST_toAList])
  \\ metis_tac[ALL_DISTINCT_MAP, ALL_DISTINCT_fmap_to_alist_keys]
QED

Definition storage_kvs_def:
  storage_kvs [] (acc: (word8 list # word8 list) list) = REVERSE acc ∧
  storage_kvs ((k:num, v:bytes32)::ls) acc =
  storage_kvs ls $
    (storage_key k, storage_value (w2n v)) :: acc
End

val () = cv_trans storage_kvs_def;

Theorem storage_kvs_thm:
  storage_kvs l acc =
  REVERSE acc ++
  MAP (λ(k,v). (storage_key k, storage_value (w2n v))) l
Proof
  qid_spec_tac`acc`
  \\ Induct_on`l`
  \\ simp[storage_kvs_def, FORALL_PROD]
QED

Definition trie_root_from_kvs_def:
  trie_root_from_kvs kvs = let
    r = patricialise_fused kvs;
    e = rlp_encode r;
  in 
    if LENGTH e < 32 then
      Keccak_256_w64 e
    else dest_RLPB r
End

val () = cv_auto_trans trie_root_from_kvs_def;

Theorem storage_root_eqn:
  storage_root (s:storage) = let
    t = build_spt 0w (dimword (:256)) s;
    l = toAList t;
    kvs = storage_kvs l [];
  in trie_root_from_kvs kvs
Proof
  rewrite_tac[trie_root_from_kvs_def, storage_root_def, storage_trie_def,
              storage_kvs_thm, expanded_storage_trie_def, trie_root_def]
  \\ BasicProvers.LET_ELIM_TAC
  \\ `PERM (MAP (n2w ## I) l) l'`
  by (
    unabbrev_all_tac
    \\ rewrite_tac[storage_fmap_def]
    \\ irule PERM_alist_build_fmap_build_spt
    \\ rw[] )
  \\ `PERM kvs kvs'`
  by (
    qmatch_asmsub_abbrev_tac`MAP f l'`
    \\ drule_then(qspec_then`f`mp_tac) PERM_MAP
    \\ rw[Abbr`kvs`, Abbr`kvs'`]
    \\ irule PERM_TRANS
    \\ goal_assum $ drule_at Any
    \\ irule PERM_INTRO
    \\ rw[MAP_MAP_o, MAP_EQ_f, FORALL_PROD, Abbr`f`]
    \\ AP_TERM_TAC
    \\ gvs[Abbr`l`, MEM_toAList]
    \\ gvs[Abbr`t`, lookup_build_spt] )
  \\ gvs[GSYM patricialise_fused_thm]
  \\ `r = root_node`
  by (
    rw[Abbr`r`, Abbr`root_node`]
    \\ rw[patricialise_fused_thm]
    \\ AP_TERM_TAC
    \\ AP_TERM_TAC
    \\ irule patricialise_PERM
    \\ rw[] )
  \\ gvs[]
QED

Definition cv_storage_root_def:
  cv_storage_root (s:cv) =
  cv_trie_root_from_kvs $
    cv_storage_kvs (cv_toAList s) (Num 0)
End

val cv_trie_root_from_kvs_thm =
  theorem"cv_trie_root_from_kvs_thm";

Theorem cv_storage_root_rep[cv_rep]:
  from_list from_word $ storage_root s =
  cv_storage_root (from_storage s)
Proof
  simp[cv_storage_root_def, storage_root_eqn,
       from_storage_def, Excl"SIZES_CONV",
       cv_trie_root_from_kvs_thm]
  \\ qmatch_goalsub_abbrev_tac`from_sptree_sptree_spt _ t`
  \\ simp[GSYM cv_toAList_thm]
  \\ simp[theorem"cv_storage_kvs_thm"]
  \\ simp[from_list_def]
QED

Definition encode_account_def:
  encode_account a = rlp_encode $ RLPL [
    rlp_number a.nonce;
    rlp_number a.balance;
    RLPB $ storage_root a.storage;
    RLPB $ Keccak_256_w64 a.code
  ]
End

Definition accounts_fmap_def:
  accounts_fmap (a: evm_accounts) : address |-> account_state =
  build_fmap empty_account_state (dimword (:160)) a
End

Definition account_key_def:
  account_key (addr: address) =
  bytes_to_nibble_list $ Keccak_256_w64 $ word_to_bytes addr T
End

Definition state_trie_def:
  state_trie (a: evm_accounts) = let
    m = accounts_fmap a;
    l = fmap_to_alist m;
    kvs = MAP (account_key ## encode_account) l;
    t = patricialise kvs
  in OPTION_MAP encode_trie_node t
End

Definition state_root_def:
  state_root a = trie_root $ state_trie a
End

Definition state_kvs_def:
  state_kvs [] acc = REVERSE acc ∧
  state_kvs ((k,v)::ls) acc =
  state_kvs ls ((account_key $ n2w k, encode_account v)::acc)
End

val () = cv_auto_trans state_kvs_def;

Theorem state_kvs_map:
  state_kvs ls acc = REVERSE acc ++ MAP (λp. account_key (n2w $ FST p),
  encode_account (SND p)) ls
Proof
  qid_spec_tac`acc`
  \\ Induct_on`ls`
  \\ rw[state_kvs_def]
  \\ Cases_on`h` \\ rw[state_kvs_def]
QED

Definition cv_state_root_def:
  cv_state_root (a:cv) =
  cv_trie_root_from_kvs $
    cv_state_kvs (cv_toAList a) (Num 0)
End

val cv_state_kvs_thm = theorem "cv_state_kvs_thm";

Theorem state_root_eqn:
  state_root (a:evm_accounts) = let
    t = build_spt empty_account_state (dimword (:160)) a;
    l = toAList t;
    kvs = state_kvs l []
  in trie_root_from_kvs kvs
Proof
  rewrite_tac[trie_root_from_kvs_def, state_root_def, state_trie_def,
              state_kvs_map, trie_root_def]
  \\ BasicProvers.LET_ELIM_TAC
  \\ `PERM (MAP (n2w ## I) l) l'`
  by (
    unabbrev_all_tac
    \\ rewrite_tac[accounts_fmap_def]
    \\ irule PERM_alist_build_fmap_build_spt
    \\ rw[] )
  \\ `PERM kvs kvs'`
  by (
    qmatch_asmsub_abbrev_tac`MAP f l'`
    \\ drule_then(qspec_then`f`mp_tac) PERM_MAP
    \\ rw[Abbr`kvs`, Abbr`kvs'`]
    \\ irule PERM_TRANS
    \\ goal_assum $ drule_at Any
    \\ irule PERM_INTRO
    \\ rw[MAP_MAP_o, MAP_EQ_f, FORALL_PROD, Abbr`f`])
  \\ gvs[GSYM patricialise_fused_thm]
  \\ `r = root_node`
  by (
    rw[Abbr`r`, Abbr`root_node`]
    \\ rw[patricialise_fused_thm]
    \\ AP_TERM_TAC
    \\ AP_TERM_TAC
    \\ rw[Abbr`t'`]
    \\ irule patricialise_PERM
    \\ rw[] )
  \\ gvs[]
QED

Theorem cv_state_root_rep[cv_rep]:
  from_list from_word $ state_root a =
  cv_state_root (from_evm_accounts a)
Proof
  simp[cv_state_root_def, state_root_eqn,
       from_evm_accounts_def, Excl"SIZES_CONV",
       cv_trie_root_from_kvs_thm]
  \\ qmatch_goalsub_abbrev_tac`from_sptree_sptree_spt _ t`
  \\ simp[GSYM cv_toAList_thm,
          state_kvs_map |> Q.GEN`acc` |> Q.SPEC`[]` |>
          SIMP_RULE (srw_ss()) [] |> GSYM]
  \\ simp[cv_state_kvs_thm |> GSYM |> Q.GEN`acc` |> Q.SPEC`[]` |>
          SIMP_RULE std_ss [from_list_def]]
QED

val _ = export_theory();
