open HolKernel boolLib bossLib Parse
     listTheory rich_listTheory combinTheory sortingTheory wordsTheory
     optionTheory arithmeticTheory finite_mapTheory sptreeTheory
     pairTheory alistTheory numposrepTheory wordsLib blastLib
     recursiveLengthPrefixTheory
     vfmTypesTheory vfmStateTheory
     cv_transLib cv_typeLib cv_typeTheory cv_stdTheory

val _ = new_theory "merkle";

(* TODO: move *)

Theorem PERM_toAList_toSortedAList:
  PERM (toAList t) (toSortedAList t)
Proof
  irule PERM_ALL_DISTINCT
  \\ conj_tac
  >- ( Cases \\ simp[MEM_toAList, MEM_toSortedAList] )
  \\ conj_tac
  >- metis_tac[ALL_DISTINCT_MAP, ALL_DISTINCT_MAP_FST_toAList]
  >- metis_tac[ALL_DISTINCT_MAP, ALL_DISTINCT_MAP_FST_toSortedAList]
QED

Theorem OPT_MMAP_IS_SOME:
  IS_SOME (OPT_MMAP f ls) ⇔ EVERY IS_SOME (MAP f ls)
Proof
  Induct_on`ls` \\ rw[]
  \\ Cases_on`f h` \\ rw[]
  \\ Cases_on`OPT_MMAP f ls` \\ gs[]
QED

Theorem NULL_MAP[simp]:
  NULL (MAP f ls) = NULL ls
Proof
  rw[NULL_EQ]
QED

Theorem PERM_NULL:
  !l1 l2. PERM l1 l2 ==> NULL l1 = NULL l2
Proof
  ho_match_mp_tac PERM_IND
  \\ rw[NULL_EQ]
QED

Theorem LENGTH_TL_LESS_EQ:
  !ls. LENGTH (TL ls) <= LENGTH ls
Proof
  Cases \\ rw[]
QED

Datatype:
  trie_node =
    Leaf      (byte list) (byte list)
  | Extension (byte list) (trie_node option)
  | Branch    (trie_node option list) (byte list)
End

Definition longest_common_prefix_def:
  longest_common_prefix [] y = [] ∧
  longest_common_prefix x [] = [] ∧
  longest_common_prefix (x::xs) (y::ys) =
  if x = y then x :: longest_common_prefix xs ys else []
End

Theorem longest_common_prefix_common_prefixes_PAIR:
  ∀x y.
  longest_common_prefix x y ∈ common_prefixes {x; y} ∧
  ∀p. p ∈ common_prefixes {x; y} ⇒ LENGTH p ≤ LENGTH $ longest_common_prefix x y
Proof
  recInduct longest_common_prefix_ind
  \\ rw[common_prefixes_PAIR, longest_common_prefix_def]
  \\ gs[]
QED

Theorem longest_common_prefix_thm:
  ∀x y.
  longest_common_prefix x y ≼ x ∧
  longest_common_prefix x y ≼ y ∧
  (∀p. p ≼ x ∧ p ≼ y ⇒ p ≼ longest_common_prefix x y)
Proof
  recInduct longest_common_prefix_ind
  \\ rw[longest_common_prefix_def]
  \\ gs[IS_PREFIX_APPEND, APPEND_EQ_CONS]
QED

Theorem longest_common_prefix_nil[simp]:
  longest_common_prefix x [] = [] ∧
  longest_common_prefix [] y = []
Proof
  rw[longest_common_prefix_def]
  \\ Cases_on`x` \\ rw[longest_common_prefix_def]
QED

Theorem longest_common_prefix_comm:
  ∀x y.
    longest_common_prefix x y =
    longest_common_prefix y x
Proof
  recInduct longest_common_prefix_ind
  \\ rw[]
  \\ rw[Once longest_common_prefix_def]
  \\ rw[Once longest_common_prefix_def, SimpRHS]
  >- first_assum MATCH_ACCEPT_TAC
  \\ rw[Once longest_common_prefix_def]
QED

Theorem longest_common_prefix_assoc:
  ∀x y z.
  longest_common_prefix (longest_common_prefix x y) z =
  longest_common_prefix x (longest_common_prefix y z)
Proof
  recInduct longest_common_prefix_ind
  \\ rw[longest_common_prefix_def]
  \\ Cases_on`z`
  \\ rw[longest_common_prefix_def]
  \\ rw[]
QED

Definition longest_common_prefix_of_list_def:
  longest_common_prefix_of_list [] = [] ∧
  longest_common_prefix_of_list [x] = x ∧
  longest_common_prefix_of_list (x::y::xs) =
  longest_common_prefix_of_list (longest_common_prefix x y :: xs)
Termination
  WF_REL_TAC`measure LENGTH` \\ gs[]
End

Theorem longest_common_prefix_of_list_thm:
  ∀ls.
  (∀x. MEM x ls ⇒
       longest_common_prefix_of_list ls ≼ x) ∧
  (¬NULL ls ⇒
   ∀lcp. (∀x. MEM x ls ⇒ lcp ≼ x) ⇒
   lcp ≼ longest_common_prefix_of_list ls)
Proof
  recInduct longest_common_prefix_of_list_ind
  \\ gs[longest_common_prefix_of_list_def]
  \\ srw_tac[boolSimps.DNF_ss][]
  \\ TRY (
    irule IS_PREFIX_TRANS
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gs[longest_common_prefix_thm] \\ NO_TAC)
  \\ last_x_assum irule
  \\ simp[longest_common_prefix_thm]
QED

Theorem longest_common_prefix_of_list_CONS:
  longest_common_prefix_of_list (x::xs) =
  if NULL xs then x else
    longest_common_prefix x $
    longest_common_prefix_of_list xs
Proof
  qid_spec_tac`x`
  \\ Induct_on`xs`
  \\ rw[longest_common_prefix_of_list_def]
  \\ rw[longest_common_prefix_assoc]
QED

Theorem longest_common_prefix_of_list_PERM:
  ∀l1 l2.
    PERM l1 l2 ⇒
    longest_common_prefix_of_list l1 =
    longest_common_prefix_of_list l2
Proof
  ho_match_mp_tac PERM_STRONG_IND
  \\ rw[longest_common_prefix_of_list_CONS]
  \\ gs[NULL_EQ, longest_common_prefix_of_list_def]
  \\ rw[AC longest_common_prefix_assoc longest_common_prefix_comm]
QED

Definition make_branch_def:
  make_branch (kvs: (byte list # byte list) list) (nb: byte) =
  MAP (TL ## I) $ FILTER (λkv. [nb] ≼ FST kv) kvs
End

Definition patricialise_def:
  patricialise [] = NONE ∧
  patricialise [(k, v)] = SOME $ Leaf k v ∧
  patricialise kvs = let
    lcp = longest_common_prefix_of_list (MAP FST kvs)
  in
    if ALL_DISTINCT (MAP FST kvs) then
    if NULL lcp then
      let
        branches = GENLIST (make_branch kvs o n2w) 16;
        values = MAP SND $ FILTER (NULL o FST) kvs;
        value = if NULL values then [] else HD values
      in
        SOME $ Branch (MAP patricialise branches) value
    else
      SOME $
      Extension lcp (patricialise (MAP (DROP (LENGTH lcp) ## I) kvs))
    else NONE
Termination
  WF_REL_TAC`measure (SUM o (MAP $ LENGTH o FST))`
  \\ gs[]
  \\ conj_tac
  >- (
    rpt gen_tac
    \\ qmatch_goalsub_abbrev_tac`make_branch kvs`
    \\ qmatch_goalsub_abbrev_tac`_ ∧ (_ ∧ M) ⇒ _`
    \\ strip_tac
    \\ `∃nb. a = make_branch kvs nb`
    by ( fs[Abbr`M`] \\ metis_tac[] )
    \\ simp[make_branch_def, MAP_MAP_o, o_DEF]
    \\ qmatch_goalsub_abbrev_tac `_ < lkvs`
    \\ `lkvs = SUM (MAP (λx. LENGTH (FST x)) kvs)`
    by ( simp[Abbr`lkvs`, Abbr`kvs`] )
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`SUM (MAP f fkvs) < SUM (MAP g kvs)`
    \\ irule LESS_EQ_LESS_TRANS
    \\ qexists_tac`SUM (MAP f kvs)`
    \\ conj_tac
    >- (
      irule SUM_MAP_same_LESS
      \\ simp[Abbr`f`, Abbr`g`, LENGTH_TL_LESS_EQ, EXISTS_MEM]
      \\ qmatch_assum_rename_tac`k1 ≠ k2`
      \\ qmatch_asmsub_rename_tac`(k1,v1)::(k2,v2)::_`
      \\ qexists_tac`if NULL k1 then (k2,v2) else (k1,v1)`
      \\ conj_tac >- rw[Abbr`kvs`]
      \\ rw[NULL_EQ]
      \\ qmatch_goalsub_rename_tac`TL tt`
      \\ Cases_on`tt` \\ gs[] )
    \\ irule SUM_SUBLIST
    \\ irule MAP_SUBLIST
    \\ qunabbrev_tac`fkvs`
    \\ irule FILTER_sublist )
  \\ rpt gen_tac
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`longest_common_prefix_of_list fkvs`
  \\ qmatch_goalsub_abbrev_tac `_ < lkvs`
  \\ `lkvs = SUM (MAP LENGTH fkvs)`
    by ( simp[Abbr`lkvs`, Abbr`fkvs`, MAP_MAP_o, o_DEF] )
  \\ qmatch_goalsub_abbrev_tac`DROP (LENGTH lcp)`
  \\ simp[MAP_MAP_o, o_DEF]
  \\ qmatch_goalsub_abbrev_tac`lhs < _`
  \\ `lhs = SUM (MAP (flip $- (LENGTH lcp) o LENGTH) fkvs)`
  by simp[Abbr`fkvs`, Abbr`lhs`, o_DEF, MAP_MAP_o]
  \\ simp[]
  \\ irule SUM_MAP_same_LESS
  \\ simp[]
  \\ `0 < LENGTH lcp` by (Cases_on`lcp` \\ gs[])
  \\ simp[Abbr`fkvs`]
  \\ qmatch_assum_rename_tac`k1 ≠ k2`
  \\ Cases_on`k1` \\ Cases_on`k2` \\ gs[]
End

Definition drop_from_keys_def:
  drop_from_keys n [] = [] ∧
  drop_from_keys n ((k, v)::kvs) =
  (DROP n k,v) :: drop_from_keys n kvs
End

Definition patricialise_list_def:
  patricialise_list [] acc = REVERSE acc ∧
  patricialise_list (b::bs) acc =
  patricialise_list bs (patricialise b :: acc)
End

Theorem patricialise_list_map:
  patricialise_list bs acc = REVERSE acc ++ MAP patricialise bs
Proof
  qid_spec_tac`acc`
  \\ Induct_on`bs`
  \\ rw[patricialise_list_def]
QED

Theorem drop_from_keys_map:
  drop_from_keys n ls = MAP (DROP n ## I) ls
Proof
  Induct_on`ls` \\ simp[drop_from_keys_def]
  \\ Cases \\ simp[drop_from_keys_def]
QED

Theorem patricialise_ALL_DISTINCT_def:
  ∀kvs. ALL_DISTINCT (MAP FST kvs) ⇒
  patricialise kvs =
  case kvs of [] => NONE
     | [(k, v)] => SOME $ Leaf k v
     | _ => let
       lcp = longest_common_prefix_of_list (MAP FST kvs) in
         if NULL lcp then
           let
             branches = GENLIST (make_branch kvs o n2w) 16;
             values = MAP SND $ FILTER (NULL o FST) kvs;
             value = if NULL values then [] else HD values
           in
             SOME $ Branch (patricialise_list branches []) value
         else
           SOME $
           Extension lcp (patricialise (drop_from_keys (LENGTH lcp) kvs))
Proof
  recInduct patricialise_ind
  \\ rpt strip_tac
  >- EVAL_TAC
  >- EVAL_TAC
  \\ rewrite_tac[patricialise_def, patricialise_list_map, drop_from_keys_map]
  \\ asm_rewrite_tac[REVERSE_DEF, APPEND]
  \\ simp_tac (std_ss ++ ETA_ss) [list_case_def]
QED

Theorem make_branch_PERM:
  PERM kvs1 kvs2 ==>
  PERM (make_branch kvs1 i) (make_branch kvs2 i)
Proof
  rw[make_branch_def]
  \\ irule PERM_MAP
  \\ irule PERM_FILTER
  \\ rw[]
QED

Theorem patricialise_PERM:
  ∀kvs1 kvs2.
    PERM kvs1 kvs2 ⇒
    patricialise kvs1 = patricialise kvs2
Proof
  recInduct patricialise_ind
  \\ conj_tac >- rw[]
  \\ conj_tac >- rw[]
  \\ rpt gen_tac
  \\ rpt strip_tac
  \\ Cases_on`kvs2` >- gs[]
  \\ qmatch_assum_rename_tac`PERM _ (_::ls)`
  \\ Cases_on`ls` >- gs[]
  \\ rewrite_tac[patricialise_def]
  \\ qmatch_assum_abbrev_tac`PERM kvs1 kvs2`
  \\ `PERM (MAP FST kvs1) (MAP FST kvs2)`
  by metis_tac[PERM_MAP]
  \\ drule longest_common_prefix_of_list_PERM
  \\ strip_tac
  \\ `ALL_DISTINCT (MAP FST kvs1) =
      ALL_DISTINCT (MAP FST kvs2)` by simp[ALL_DISTINCT_PERM]
  \\ BasicProvers.LET_ELIM_TAC
  \\ simp[]
  \\ IF_CASES_TAC \\ simp[]
  \\ reverse IF_CASES_TAC \\ simp[]
  >- (
    first_x_assum irule
    \\ simp[]
    \\ irule PERM_MAP
    \\ simp[] )
  \\ reverse conj_tac
  >- (
    simp[Abbr`value`, Abbr`value'`]
    \\ simp[Abbr`values`, Abbr`values'`]
    \\ qmatch_goalsub_abbrev_tac`FILTER P`
    \\ `PERM (FILTER P kvs1) (FILTER P kvs2)` by simp[PERM_FILTER]
    \\ drule PERM_NULL
    \\ simp[] \\ strip_tac
    \\ IF_CASES_TAC \\ simp[]
    \\ `∃k v. FILTER P kvs1  = [(k, v)]`
    by (
      Cases_on`FILTER P kvs1` \\ gs[]
      \\ fs[FILTER_EQ_CONS, FILTER_EQ_NIL]
      \\ qmatch_assum_rename_tac`P kv`
      \\ Cases_on`kv` \\ gs[]
      \\ qmatch_rename_tac`ls = []`
      \\ Cases_on`ls` \\ gs[]
      \\ gvs[FILTER_EQ_CONS]
      \\ gvs[Abbr`P`, NULL_EQ]
      \\ gvs[ALL_DISTINCT_APPEND] )
    \\ gs[] )
  \\ simp[LIST_EQ_REWRITE]
  \\ conj_asm1_tac >- rw[Abbr`branches`, Abbr`branches'`]
  \\ simp[EL_MAP]
  \\ rpt strip_tac
  \\ last_x_assum irule
  \\ simp[]
  \\ conj_tac >- metis_tac[MEM_EL]
  \\ qmatch_asmsub_abbrev_tac`GENLIST _ st`
  \\ gs[Abbr`branches`, Abbr`branches'`, EL_GENLIST]
  \\ irule make_branch_PERM
  \\ rw[]
QED

Datatype:
  rlp = RLPB (word8 list) | RLPL (rlp list)
End

Definition dest_RLPB_def:
  dest_RLPB (RLPB bs) = bs ∧
  dest_RLPB _ = []
End

Datatype:
  encoded_trie_node =
    MTL (byte list) (byte list)
  | MTE (byte list) rlp
  | MTB (rlp list) (byte list)
End

Definition nibble_list_to_bytes_def:
  nibble_list_to_bytes ([]: byte list) = [] : byte list ∧
  nibble_list_to_bytes [n] = [n] ∧
  nibble_list_to_bytes (n1::n2::ns) =
  ((n1 << 4) || n2) :: nibble_list_to_bytes ns
End

Definition bytes_to_nibble_list_def:
  bytes_to_nibble_list [] = [] : word8 list ∧
  bytes_to_nibble_list (b::bs) =
  ((b && 0xf0w) >>> 4) :: (b && 0x0fw) :: bytes_to_nibble_list bs
End

Theorem bytes_to_nibble_list_to_bytes:
  nibble_list_to_bytes (bytes_to_nibble_list bs) = bs
Proof
  Induct_on`bs`
  \\ rw[nibble_list_to_bytes_def, bytes_to_nibble_list_def]
  \\ BBLAST_TAC
QED

Theorem bytes_to_nibble_list_nibbles:
  EVERY (λn. n && 0xf0w = 0w) (bytes_to_nibble_list bs)
Proof
  Induct_on`bs` \\ gs[bytes_to_nibble_list_def]
QED

Theorem nibble_list_to_bytes_to_nibble_list:
  EVEN (LENGTH ns) ∧ EVERY (λn. n && 0xf0w = 0w) ns ⇒
  bytes_to_nibble_list (nibble_list_to_bytes ns) = ns
Proof
  completeInduct_on`LENGTH ns`
  \\ rw[]
  \\ Cases_on`ns`
  \\ rw[bytes_to_nibble_list_def, nibble_list_to_bytes_def]
  \\ Cases_on`t` \\ gs[]
  \\ qmatch_goalsub_rename_tac`n1::n2::ns`
  \\ simp[bytes_to_nibble_list_def, nibble_list_to_bytes_def]
  \\ rpt (
    conj_tac >- (
      rpt (qpat_x_assum`_ = 0w`mp_tac)
      \\ BBLAST_TAC ))
  \\ first_x_assum irule
  \\ rw[]
  \\ gs[ADD1, EVEN_ADD]
QED

Definition nibble_list_to_compact_def:
  nibble_list_to_compact bytes isLeaf =
  if EVEN (LENGTH bytes) then
    (16w * (if isLeaf then 2w else 0w)) ::
    nibble_list_to_bytes bytes
  else
    16w * (if isLeaf then 3w else 1w) + HD bytes ::
    nibble_list_to_bytes (TL bytes)
End

(* TODO: move out of vfmCompute *)
val () = cv_auto_trans Keccak_256_bytes_def;

val () = cv_auto_trans nibble_list_to_bytes_def;
val nibble_list_to_compact_pre_def = cv_trans_pre nibble_list_to_compact_def;

Theorem nibble_list_to_compact_pre[cv_pre]:
  nibble_list_to_compact_pre x y
Proof
  rw[nibble_list_to_compact_pre_def]
  \\ strip_tac \\ gs[]
QED

Definition rlp_encode_def:
  rlp_encode (RLPB bs) = rlp_bytes bs ∧
  rlp_encode (RLPL rs) = rlp_encode_list [] rs ∧
  rlp_encode_list acc [] = rlp_list $ FLAT $ REVERSE acc ∧
  rlp_encode_list acc (x::xs) =
  rlp_encode_list (rlp_encode x :: acc) xs
End

val () = cv_auto_trans rlp_encode_def;

Definition encode_internal_node_unencoded_def:
  encode_internal_node_unencoded NONE = RLPB [] ∧
  encode_internal_node_unencoded (SOME (MTL key value)) =
    RLPL [RLPB $ nibble_list_to_compact key T; RLPB value] ∧
  encode_internal_node_unencoded (SOME (MTE key subnode)) =
    RLPL [RLPB $ nibble_list_to_compact key F; subnode] ∧
  encode_internal_node_unencoded (SOME (MTB subnodes value)) =
    RLPL $ SNOC (RLPB value) subnodes
End

Definition encode_internal_node_def:
  encode_internal_node node = let
    unencoded = encode_internal_node_unencoded node;
    encoded = rlp_encode unencoded
  in
    if LENGTH encoded < 32 then unencoded
    else RLPB $ Keccak_256_bytes encoded
End

val () = cv_auto_trans encode_internal_node_def;

Definition encode_trie_node_def:
  encode_trie_node (Leaf key value) =
    MTL key value ∧
  encode_trie_node (Extension key node) =
    MTE key $
    encode_internal_node (OPTION_MAP encode_trie_node node) ∧
  encode_trie_node (Branch nodes value) =
    MTB
      (MAP (encode_internal_node o OPTION_MAP encode_trie_node) nodes)
       value
Termination
  WF_REL_TAC `measure trie_node_size`
End

Definition encode_trie_node_fo_def:
  encode_trie_node_fo (Leaf k v) = MTL k v ∧
  encode_trie_node_fo (Extension k n) =
  (let t = case n of NONE => NONE | SOME n => SOME $ encode_trie_node_fo n in
    MTE k (encode_internal_node t)) ∧
  encode_trie_node_fo (Branch ns v) =
  (let ts = encode_trie_node_fo_list ns in
    MTB (MAP encode_internal_node ts) v) ∧
  encode_trie_node_fo_list [] = [] ∧
  encode_trie_node_fo_list (x::xs) =
  (let n = case x of NONE => NONE | SOME n => SOME $ encode_trie_node_fo n in
    n :: encode_trie_node_fo_list xs)
Termination
  WF_REL_TAC`measure (λx. case x of INR ls => trie_node1_size ls |
                                    INL t => trie_node_size t)`
End

Theorem encode_trie_node_fo_thm:
  (∀t. encode_trie_node_fo t = encode_trie_node t) ∧
  (∀ls. encode_trie_node_fo_list ls = MAP (OPTION_MAP encode_trie_node) ls)
Proof
  ho_match_mp_tac encode_trie_node_fo_ind
  \\ rw[encode_trie_node_def, encode_trie_node_fo_def]
  \\ srw_tac[ETA_ss][MAP_MAP_o]
  \\ CASE_TAC \\ gs[]
QED

val () = cv_auto_trans encode_trie_node_fo_def;

Definition build_fmap_def:
  build_fmap z 0 m = FEMPTY ∧
  build_fmap z (SUC n) m =
  if m (n2w n) = z then build_fmap z n m
  else FUPDATE (build_fmap z n m) (n2w n, (m (n2w n)))
End

Theorem build_fmap_empty:
  (∀x. x < n ⇒ m (n2w x) = z) ⇒
  build_fmap z n m = FEMPTY
Proof
  Induct_on`n` \\ rw[build_fmap_def]
QED

Theorem lookup_build_fmap:
  ∀n k. n ≤ dimword(:'a) ⇒
  FLOOKUP (build_fmap z n m) (k:α word) =
  if n ≤ w2n k then NONE
  else if m k = z then NONE
  else SOME (m k)
Proof
  Induct \\ gvs[build_fmap_def]
  \\ rw[FLOOKUP_UPDATE, LESS_OR_EQ]
  \\ gvs[NOT_LESS] \\ rw[] \\ gvs[]
  \\ strip_tac \\ gvs[]
  \\ Cases_on`n < dimword(:'a)` \\ gs[]
  \\ `0 < dimword(:'a)` by gs[]
  \\ `SUC n < dimword(:'a)` by gs[]
  \\ gs[]
QED

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

Definition expanded_storage_trie_def:
  expanded_storage_trie s = let
    m = storage_fmap s;
    l = fmap_to_alist m;
    kvs = MAP (λ(k,v). (MAP n2w $ word_to_hex_list k, MAP n2w $ w2l 256 v)) l
  in patricialise kvs
End

Definition storage_trie_def:
  storage_trie s = OPTION_MAP encode_trie_node $ expanded_storage_trie s
End

Definition trie_root_def:
  trie_root t = let
    root_node = encode_internal_node t;
    encoded = rlp_encode root_node
  in
    if LENGTH encoded < 32 then
      Keccak_256_bytes encoded
    else
      dest_RLPB root_node
End

Definition storage_root_def:
  storage_root s = trie_root $ storage_trie s
End

Theorem make_branch_eta[local]:
  make_branch kvs nb =
  MAP (λp. (TL (FST p), SND p)) $ FILTER (λkv. [nb] ≼ FST kv) kvs
Proof
  rw[make_branch_def]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ rw[FUN_EQ_THM, PAIR_MAP]
QED

val () = make_branch_eta |> cv_auto_trans;
val () = longest_common_prefix_of_list_def |> cv_auto_trans;

Definition patricialise_fused_clocked_def:
  patricialise_fused_clocked n kvs =
  (if n = 0n then NONE else
  (case kvs of
     | [] => SOME $ encode_internal_node NONE
     | [(k,v)] => SOME $ encode_internal_node $ SOME $ MTL k v
     | _ => let lcp = longest_common_prefix_of_list (MAP FST kvs) in
       if NULL lcp then let
         branches = GENLIST (make_branch kvs o n2w) 16;
         values = MAP SND (FILTER (NULL o FST) kvs);
         value = if NULL values then [] else HD values
         in case
           patricialise_fused_clocked_mmap (n - 1) branches []
         of NONE => NONE |
            SOME subnodes =>
            SOME $ encode_internal_node $ SOME $ MTB subnodes value
       else
         case patricialise_fused_clocked (n - 1)
                     (drop_from_keys (LENGTH lcp) kvs)
         of SOME subnode =>
            SOME $ encode_internal_node $ SOME $ MTE lcp subnode
          | NONE => NONE)) ∧
  patricialise_fused_clocked_mmap 0 _ _ = NONE ∧
  patricialise_fused_clocked_mmap n [] acc = SOME (REVERSE acc) ∧
  patricialise_fused_clocked_mmap n (b::bs) acc =
    case patricialise_fused_clocked (n - 1) b of NONE => NONE
       | SOME a => patricialise_fused_clocked_mmap (n - 1) bs (a::acc)
Termination
  WF_REL_TAC`measure (λx. case x of INL p => FST p | INR p => FST p)`
End

Theorem patricialise_fused_clocked_add:
  (∀n kvs m.
     patricialise_fused_clocked n kvs ≠ NONE ⇒
     patricialise_fused_clocked (n + m) kvs =
     patricialise_fused_clocked n kvs) ∧
  (∀n bs acc m.
     patricialise_fused_clocked_mmap n bs acc ≠ NONE ⇒
     patricialise_fused_clocked_mmap (n + m) bs acc =
     patricialise_fused_clocked_mmap n bs acc)
Proof
  ho_match_mp_tac patricialise_fused_clocked_ind
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ gen_tac
    \\ rewrite_tac[Once patricialise_fused_clocked_def]
    \\ IF_CASES_TAC >- rw[]
    \\ BasicProvers.TOP_CASE_TAC
    >- rw[patricialise_fused_clocked_def]
    \\ BasicProvers.TOP_CASE_TAC
    >- rw[patricialise_fused_clocked_def]
    \\ qmatch_goalsub_abbrev_tac`GENLIST _ nb`
    \\ strip_tac
    \\ rewrite_tac[Once patricialise_fused_clocked_def]
    \\ IF_CASES_TAC >- gs[]
    \\ qmatch_goalsub_abbrev_tac`lhs = _`
    \\ rewrite_tac[Once patricialise_fused_clocked_def]
    \\ IF_CASES_TAC >- gs[]
    \\ qunabbrev_tac`lhs`
    \\ simp_tac std_ss [list_case_def]
    \\ qmatch_goalsub_abbrev_tac`MAP FST kvs`
    \\ asm_simp_tac std_ss []
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`NULL lcp`
    \\ IF_CASES_TAC
    >- (
      simp[]
      \\ AP_THM_TAC
      \\ AP_THM_TAC
      \\ AP_TERM_TAC
      \\ `m + n - 1 = n - 1 + m` by ( Cases_on`n` \\ gs[] )
      \\ pop_assum SUBST_ALL_TAC
      \\ last_x_assum irule
      \\ gs[]
      \\ simp[Abbr`kvs`]
      \\ fs[CaseEq"option"] )
    \\ simp[]
    \\ AP_THM_TAC
    \\ AP_THM_TAC
    \\ AP_TERM_TAC
    \\ `m + n - 1 = n - 1 + m` by ( Cases_on`n` \\ gs[] )
    \\ pop_assum SUBST_ALL_TAC
    \\ first_x_assum irule
    \\ gs[]
    \\ reverse conj_tac >- rw[Abbr`kvs`]
    \\ strip_tac \\ fs[])
  \\ conj_tac >- rw[Once patricialise_fused_clocked_def]
  \\ conj_tac >- (
    rw[patricialise_fused_clocked_def]
    \\ qmatch_goalsub_rename_tac`m + SUC n`
    \\ `m + SUC n = SUC (m + n)` by simp[]
    \\ rw[patricialise_fused_clocked_def] )
  \\ rw[]
  \\ qmatch_goalsub_rename_tac`m + SUC n`
  \\ `m + SUC n = SUC (m + n)` by simp[]
  \\ pop_assum SUBST_ALL_TAC
  \\ pop_assum mp_tac
  \\ rw[Once patricialise_fused_clocked_def]
  \\ rw[Once patricialise_fused_clocked_def]
  \\ rw[Once patricialise_fused_clocked_def, SimpRHS]
  \\ irule EQ_SYM
  \\ BasicProvers.TOP_CASE_TAC \\ gs[]
QED

Theorem patricialise_fused_clocked_mmap_thm:
  ∀bs n acc as.
    LENGTH bs < n ∧
    GENLIST (λi. patricialise_fused_clocked (n - i - 1) (EL i bs)) (LENGTH bs) =
      MAP SOME as ⇒
    patricialise_fused_clocked_mmap n bs acc = SOME (REVERSE acc ++ as)
Proof
  Induct \\ rw[]
  >- ( Cases_on`n` \\ gs[Once patricialise_fused_clocked_def] )
  \\ Cases_on`n` \\ gs[]
  \\ simp[Once patricialise_fused_clocked_def]
  \\ gs[GENLIST_CONS]
  \\ Cases_on`as` \\ gs[]
  \\ qmatch_goalsub_rename_tac`REVERSE acc ++ a :: as`
  \\ `REVERSE acc ++ a :: as = REVERSE (a::acc) ++ as` by rw[]
  \\ pop_assum SUBST_ALL_TAC
  \\ first_x_assum irule
  \\ simp[]
  \\ pop_assum(SUBST1_TAC o SYM)
  \\ simp[LIST_EQ_REWRITE, ADD1]
QED

Theorem patricialise_fused_clocked_thm:
  ∀kvs. ALL_DISTINCT (MAP FST kvs) ⇒
    ∃n. patricialise_fused_clocked n kvs
        = SOME $ encode_internal_node $ OPTION_MAP encode_trie_node $ patricialise kvs
Proof
  recInduct patricialise_ind
  \\ conj_tac
  >- rw[patricialise_def, patricialise_fused_clocked_def]
  \\ conj_tac
  >- rw[patricialise_def, patricialise_fused_clocked_def, encode_trie_node_def]
  \\ rpt gen_tac \\ strip_tac
  \\ once_rewrite_tac[patricialise_def]
  \\ qmatch_goalsub_abbrev_tac`MAP FST kvs`
  \\ qmatch_goalsub_abbrev_tac`GENLIST _ nb`
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`NULL lcp`
  \\ strip_tac
  \\ asm_simp_tac std_ss [Once patricialise_fused_clocked_def]
  \\ simp[Once EXISTS_NUM]
  \\ qunabbrev_tac`kvs`
  \\ simp_tac std_ss [list_case_def]
  \\ qmatch_goalsub_abbrev_tac`FILTER _ kvs`
  \\ Cases_on`NULL lcp` \\ simp[]
  >- (
    simp[encode_trie_node_def, MAP_MAP_o, CaseEq"option"]
    \\ qmatch_goalsub_abbrev_tac`MTB subnodes _`
    \\ qmatch_goalsub_abbrev_tac`patricialise_fused_clocked_mmap _ bs`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`subnodes` \\ simp[]
    \\ last_x_assum(qspec_then`lcp`mp_tac)
    \\ simp[]
    \\ cheat (* use patricialise_fused_clocked_thm and
                    patricialise_fused_clocked_add *) )
  \\ gs[GSYM drop_from_keys_map, CaseEq"option"]
  \\ simp[encode_trie_node_def]
  \\ qmatch_goalsub_abbrev_tac`MTE lcp subnode`
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`subnode` \\ simp[]
  \\ qunabbrev_tac`subnode`
  \\ simp[ETA_AX]
  \\ first_x_assum irule
  \\ simp[drop_from_keys_map]
  \\ cheat (* removing longest_common_prefix_of_list preserves distinct *)
QED

val patricialise_fused_clocked_pre_def =
  cv_auto_trans_pre patricialise_fused_clocked_def;

Theorem patricialise_fused_clocked_pre[cv_pre]:
  (∀n kvs. patricialise_fused_clocked_pre n kvs) ∧
  (∀v0 v v1. patricialise_fused_clocked_mmap_pre v0 v v1)
Proof
  ho_match_mp_tac patricialise_fused_clocked_ind
  \\ conj_tac
  >- (
    rpt strip_tac
    \\ rewrite_tac[Once patricialise_fused_clocked_pre_def]
    \\ strip_tac \\ rpt gen_tac \\ strip_tac
    \\ rpt gen_tac \\ strip_tac
    \\ rpt gen_tac \\ strip_tac
    \\ conj_tac
    >- (
      strip_tac \\ gen_tac
      \\ strip_tac \\ gen_tac
      \\ strip_tac
      \\ conj_tac >- rw[NULL_EQ]
      \\ gen_tac \\ strip_tac
      \\ first_x_assum irule
      \\ rpt BasicProvers.VAR_EQ_TAC
      \\ qmatch_goalsub_abbrev_tac`GENLIST _ nb`
      \\ simp[genlist_eq_GENLIST] )
    \\ strip_tac
    \\ first_x_assum irule
    \\ rpt BasicProvers.VAR_EQ_TAC
    \\ simp[] )
  \\ conj_tac
  >- rw[Once patricialise_fused_clocked_pre_def]
  \\ conj_tac
  >- rw[Once patricialise_fused_clocked_pre_def]
  \\ rpt gen_tac \\ strip_tac
  \\ simp[Once patricialise_fused_clocked_pre_def]
  \\ gs[ADD1]
QED

Definition trie_root_clocked_def:
  trie_root_clocked n kvs =
  case patricialise_fused_clocked n kvs of
    NONE => NONE
  | SOME r => SOME $
    let e = rlp_encode r in
    if LENGTH e < 32 then Keccak_256_bytes e else dest_RLPB r
End

val () = cv_auto_trans trie_root_clocked_def;

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

Definition storage_key_bytes_def:
  storage_key_bytes k : word8 list =
  MAP n2w (n2l 16 k)
End

val () = cv_auto_trans storage_key_bytes_def;

Definition storage_value_bytes_def:
  storage_value_bytes (v: bytes32) : word8 list =
  MAP n2w (w2l 256 v)
End

val () = cv_auto_trans storage_value_bytes_def;

Definition storage_kvs_def:
  storage_kvs [] (acc: (word8 list # word8 list) list) = REVERSE acc ∧
  storage_kvs ((k:num, v:bytes32)::ls) acc =
  storage_kvs ls $
    (storage_key_bytes k,
     storage_value_bytes v) :: acc
End

val () = cv_trans storage_kvs_def;

Theorem storage_kvs_thm:
  storage_kvs l acc =
  REVERSE acc ++
  MAP (λ(k,v). (MAP n2w (n2l 16 k),
                MAP n2w (w2l 256 v))) l
Proof
  qid_spec_tac`acc`
  \\ Induct_on`l`
  \\ simp[storage_kvs_def, FORALL_PROD,
          storage_key_bytes_def, storage_value_bytes_def]
QED

Definition storage_root_clocked_def:
  storage_root_clocked n (s:storage) = let
    t = build_spt 0w (dimword (:256)) s;
    l = toAList t
  in trie_root_clocked n $ storage_kvs l []
End

Theorem storage_root_clocked_thm:
  ∃n. storage_root_clocked n s = SOME $ storage_root s
Proof
  simp[storage_root_clocked_def, Excl"SIZES_CONV",
       storage_trie_def, storage_root_def, storage_kvs_thm,
       trie_root_clocked_def, trie_root_def]
  \\ qmatch_goalsub_abbrev_tac`rlp_encode r`
  \\ qmatch_goalsub_abbrev_tac`patricialise_fused_clocked _ kvs`
  \\ `ALL_DISTINCT (MAP FST kvs)`
  by (
    simp[Abbr`kvs`, MAP_MAP_o, o_DEF, UNCURRY, Excl"SIZES_CONV"]
    \\ qmatch_goalsub_abbrev_tac`build_spt _ n`
    \\ simp[GSYM MAP_MAP_o, GSYM o_DEF]
    \\ irule ALL_DISTINCT_MAP_INJ
    \\ conj_tac
    >- (
      rw[LIST_EQ_REWRITE]
      \\ gvs[EL_MAP, MEM_MAP, Excl"SIZES_CONV"]
      \\ gs[word_to_hex_list_def, w2l_def, EL_n2l, Excl"SIZES_CONV", dimword_8]
      \\ first_x_assum drule
      \\ simp[MOD_MOD_LESS_EQ] )
    \\ irule ALL_DISTINCT_MAP_INJ
    \\ conj_tac
    >- (
      rw[]
      \\ `1 < 16n` by simp[]
      \\ metis_tac[l2n_n2l] )
    \\ metis_tac[ALL_DISTINCT_MAP_FST_toAList] )
  \\ drule patricialise_fused_clocked_thm
  \\ strip_tac
  \\ qexists_tac`n`
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[Excl"SIZES_CONV"]
  \\ qmatch_goalsub_abbrev_tac`rlp_encode r2`
  \\ `r2 = r` suffices_by rw[]
  \\ qunabbrev_tac`r`
  \\ qunabbrev_tac`r2`
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ simp[expanded_storage_trie_def]
  \\ irule patricialise_PERM
  \\ qunabbrev_tac`kvs`
  \\ simp[storage_fmap_def, Excl"SIZES_CONV"]
  \\ qmatch_goalsub_abbrev_tac`PERM (MAP g sl) (MAP f fl)`
  \\ `MAP g sl = MAP (f o (n2w ## I)) sl`
  by simp[MAP_EQ_f, Abbr`g`, Abbr`f`, FORALL_PROD, word_to_hex_list_def,
          w2l_def, Excl"SIZES_CONV", Abbr`sl`, MEM_toAList, lookup_build_spt]
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[GSYM MAP_MAP_o]
  \\ irule PERM_MAP
  \\ qunabbrev_tac`fl`
  \\ qunabbrev_tac`sl`
  \\ irule PERM_alist_build_fmap_build_spt
  \\ simp[]
QED

Definition cv_storage_root_clocked_def:
  cv_storage_root_clocked (n:cv) (s:cv) =
  cv_trie_root_clocked n $
    cv_storage_kvs (cv_toAList s) (Num 0)
End

val cv_storage_kvs_thm = theorem "cv_storage_kvs_thm";
val cv_patricialise_fused_clocked_thm =
  theorem "cv_patricialise_fused_clocked_thm";
val cv_trie_root_clocked_thm = theorem "cv_trie_root_clocked_thm";

Theorem cv_storage_root_clocked_rep[cv_rep]:
  from_option (from_list from_word) $ storage_root_clocked n s =
  cv_storage_root_clocked (Num n) (from_storage s)
Proof
  simp[cv_storage_root_clocked_def, storage_root_clocked_def,
       from_storage_def, Excl"SIZES_CONV", cv_trie_root_clocked_thm]
  \\ qmatch_goalsub_abbrev_tac`from_sptree_sptree_spt _ t`
  \\ simp[GSYM cv_toAList_thm]
  \\ simp[cv_storage_kvs_thm |> GSYM |> Q.GEN`acc` |> Q.SPEC`[]` |>
          SIMP_RULE std_ss [from_list_def]]
QED

(*

Definition hex_to_rev_bytes_def:
    hex_to_rev_bytes acc [] = acc : byte list
  ∧ hex_to_rev_bytes acc [c] = CONS (n2w (UNHEX c)) acc
  ∧ hex_to_rev_bytes acc (c1::c2::rest) =
    hex_to_rev_bytes (CONS (n2w (16 * UNHEX c1 + UNHEX c2)) acc) rest
End

val _ = cv_auto_trans hex_to_rev_bytes_def;

(* empty trie root *)

val root = cv_eval ``trie_root_clocked 60 []`` |> concl |> rhs

val correct_root = cv_eval ``
REVERSE $ hex_to_rev_bytes []
  "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"``

(* empty key, non-empty value *)

val kvs = ``[[], [1w]] : (word8 list # word8 list) list``
val correct_root = cv_eval ``REVERSE $ hex_to_rev_bytes []
  "ce8c4b060e961e285a1c2d6af956fae96986f946102f23b71506524eea9e2450"``;
val root = cv_eval ``trie_root_clocked 20 ^kvs``;

(* non-empty key, non-empty value *)

val kvs = ``[[0w; 1w], [1w]] : (word8 list # word8 list) list``
val correct_root = cv_eval ``REVERSE $ hex_to_rev_bytes []
  "bb0a9dc519f763a6ffa8b82bc000baab4c8015d20ff830c548ea9cd857ea42cf"``;
val root = cv_eval ``trie_root_clocked 20 ^kvs``;

(* two keys no common prefix *)

val kvs = ``[([0w; 1w], [1w]); ([1w; 0w], [2w])] : (word8 list # word8 list) list``
val correct_root = cv_eval ``REVERSE $ hex_to_rev_bytes []
  "fae9ea07da94adc433a0b5590a7f45aa36bf80938d29a629c62929804be96cef"``;
val root = cv_eval ``trie_root_clocked 20 ^kvs``;

(* two keys with prefix *)

val kvs = ``[([0w; 1w], [1w]); ([], [2w])] : (word8 list # word8 list) list``
val correct_root = cv_eval ``REVERSE $ hex_to_rev_bytes []
  "b56ea9ac6de00cb85727dafab1ae09d5272d82564ba5b29972f6cf67dd503768"``;
val root = cv_eval ``trie_root_clocked 20 ^kvs``;

(* kvs from strings *)

val kvs = EVAL``
  MAP (bytes_to_nibble_list o MAP (n2w o ORD) ## MAP (n2w o ORD)) [
    ("a", "b")
  ] : (word8 list # word8 list) list`` |> concl |> rhs;
val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "09ca68268104f67d9da9c8514ebdd8c98c6667aba87016f8602a1fbefb575216"``;
val root = cv_eval``trie_root_clocked 40 ^kvs``;

(* building up example *)

val kvs = EVAL``
  MAP (bytes_to_nibble_list o MAP (n2w o ORD) ## MAP (n2w o ORD)) [
    ("do", "verb")
  ] : (word8 list # word8 list) list`` |> concl |> rhs;
val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "014f07ed95e2e028804d915e0dbd4ed451e394e1acfd29e463c11a060b2ddef7"``;
val root = cv_eval``trie_root_clocked 40 ^kvs``;

val kvs = EVAL``
  MAP (bytes_to_nibble_list o MAP (n2w o ORD) ## MAP (n2w o ORD)) [
    ("do", "verb");
    ("dog", "puppy")
  ] : (word8 list # word8 list) list`` |> concl |> rhs;
val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "779db3986dd4f38416bfde49750ef7b13c6ecb3e2221620bcad9267e94604d36"``;
val root = cv_eval``trie_root_clocked 40 ^kvs``;

val kvs = EVAL``
  MAP (bytes_to_nibble_list o MAP (n2w o ORD) ## MAP (n2w o ORD)) [
    ("do", "verb");
    ("dog", "puppy");
    ("doge", "coins")
  ] : (word8 list # word8 list) list`` |> concl |> rhs;
val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "1845cb4d335234906848274dcfce956c57f0c4d8f9e4aa81437c61604696d353"``;
val root = cv_eval``trie_root_clocked 40 ^kvs``;

val kvs = EVAL``
  MAP (bytes_to_nibble_list o MAP (n2w o ORD) ## MAP (n2w o ORD)) [
    ("do", "verb");
    ("horse", "stallion")
  ] : (word8 list # word8 list) list`` |> concl |> rhs;
val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "8bcc171eb7e7303059b303ef4b2c440588b534701512413785fb061ffb6e415b"``;
val root = cv_eval``trie_root_clocked 40 ^kvs``;

val kvs = EVAL``
  MAP (bytes_to_nibble_list o MAP (n2w o ORD) ## MAP (n2w o ORD)) [
    ("dog", "puppy");
    ("horse", "stallion")
  ] : (word8 list # word8 list) list`` |> concl |> rhs;
val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "ebf5de461c566173ef3f27e26d180c23125f69a517865c312c0dcd9bb0c7cbed"``;
val root = cv_eval``trie_root_clocked 40 ^kvs``;

val kvs = EVAL``
  MAP (bytes_to_nibble_list o MAP (n2w o ORD) ## MAP (n2w o ORD)) [
    ("do", "verb");
    ("dog", "puppy");
    ("horse", "stallion")
  ] : (word8 list # word8 list) list`` |> concl |> rhs;
val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "40b4a841a5ed78d2beb33a3dbba6dd38f5b1566db97ae643e073ded3aa77dceb"``;
val root = cv_eval``trie_root_clocked 40 ^kvs``;

(* example *)

val kvs = EVAL``
  MAP (bytes_to_nibble_list o MAP (n2w o ORD) ## MAP (n2w o ORD)) [
    ("do", "verb");
    ("dog", "puppy");
    ("doge", "coins");
    ("horse", "stallion")
  ] : (word8 list # word8 list) list`` |> concl |> rhs;
val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "4034a3e31976c08463970a25a9b52209bfe55ae5b503005ad77a748a2b1b4f51"``
val root = cv_eval ``trie_root_clocked 40 ^kvs`` |> concl |> rhs |> rand;

(*
  "insert-middle-leaf": {
    "in": [
      [ "key1aa", "0123456789012345678901234567890123456789xxx"],
      [ "key1", "0123456789012345678901234567890123456789Very_Long"],
      [ "key2bb", "aval3"],
      [ "key2", "short"],
      [ "key3cc", "aval3"],
      [ "key3","1234567890123456789012345678901"]
    ],
    "root": "0xcb65032e2f76c48b82b5c24b3db8f670ce73982869d38cd39a624f23d62a9e89"
  },
*)

val kvs = EVAL``
  MAP (bytes_to_nibble_list o MAP (n2w o ORD) ## MAP (n2w o ORD)) [
    ("key1aa", "0123456789012345678901234567890123456789xxx");
    ("key1", "0123456789012345678901234567890123456789Very_Long");
    ("key2bb", "aval3");
    ("key2", "short");
    ("key3cc", "aval3");
    ("key3", "1234567890123456789012345678901")
  ] : (word8 list # word8 list) list
  `` |> concl |> rhs;

val correct_root = cv_eval
``REVERSE $ hex_to_rev_bytes []
  "cb65032e2f76c48b82b5c24b3db8f670ce73982869d38cd39a624f23d62a9e89"``
  |> concl |> rhs

val root = cv_eval ``trie_root_clocked 60 ^kvs``

(*
emptyValues test
      ["do", "verb"],
      ["ether", "wookiedoo"],
      ["horse", "stallion"],
      ["shaman", "horse"],
      ["doge", "coin"],
      ["ether", null],
      ["dog", "puppy"],
      ["shaman", null]
    "root": "0x5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84"
*)

val kvs = EVAL``
  MAP (bytes_to_nibble_list o MAP (n2w o ORD) ## MAP (n2w o ORD)) [
    ("do", "verb");
    (*("ether", "wookiedoo");*)
    ("horse", "stallion");
    (*("shaman", "horse");*)
    ("doge", "coin");
    (*("ether", "");*)
    ("dog", "puppy")(*;
    ("shaman", "")*)
  ] : (word8 list # word8 list) list
  `` |> concl |> rhs;

val correct_root = cv_eval
``REVERSE $ hex_to_rev_bytes []
  "5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84"``
  |> concl |> rhs

val root = cv_eval ``trie_root_clocked 60 ^kvs`` |> concl |> rhs

*)

val _ = export_theory();
