open HolKernel boolLib bossLib Parse
     listTheory rich_listTheory combinTheory sortingTheory wordsTheory
     optionTheory arithmeticTheory finite_mapTheory sptreeTheory pairTheory
     recursiveLengthPrefixTheory
     vfmTypesTheory vfmStateTheory
     cv_transLib

val _ = new_theory "merkle";

(* TODO: move *)

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
  encoded_trie_node =
    MTL (byte list) (byte list)
  | MTE (byte list) (byte list)
  | MTB (byte list list) (byte list)
End

Definition nibble_list_to_bytes_def:
  nibble_list_to_bytes ([]: byte list) = [] : byte list ∧
  nibble_list_to_bytes [n] = [n] ∧
  nibble_list_to_bytes (n1::n2::ns) =
  16w * n1 + n2 :: nibble_list_to_bytes ns
End

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

Definition encode_internal_node_unencoded_def:
  encode_internal_node_unencoded NONE = [] ∧
  encode_internal_node_unencoded (SOME (MTL key value)) =
    [nibble_list_to_compact key T; value] ∧
  encode_internal_node_unencoded (SOME (MTE key subnode)) =
    [nibble_list_to_compact key F; subnode] ∧
  encode_internal_node_unencoded (SOME (MTB subnodes value)) =
    SNOC value subnodes
End

Definition encode_internal_node_def:
  encode_internal_node node = let
    unencoded = encode_internal_node_unencoded node;
    encoded = rlp_list (FLAT (MAP rlp_bytes unencoded))
  in
    if LENGTH encoded < 32 then encoded
    else Keccak_256_bytes encoded
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
Definition build_fmap_def:
  build_fmap z 0 m = FEMPTY ∧
  build_fmap z (SUC n) m =
  if m (n2w n) = z then build_fmap z n m
  else FUPDATE (build_fmap z n m) (n2w n, (m (n2w n)))
End

val () = cv_auto_trans encode_trie_node_fo_def;

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

Definition storage_root_def:
  storage_root s = encode_internal_node $ storage_trie s
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
         OPT_MMAP (patricialise_fused_clocked (n - 1)) branches
         of NONE => NONE |
            SOME subnodes =>
            SOME $ encode_internal_node $ SOME $ MTB subnodes value
       else
         case patricialise_fused_clocked (n - 1)
                     (drop_from_keys (LENGTH lcp) kvs)
         of SOME subnode =>
            SOME $ encode_internal_node $ SOME $ MTE lcp subnode
          | NONE => NONE))
End

Theorem patricialise_fused_clocked_add:
  ∀n kvs m.
    patricialise_fused_clocked n kvs ≠ NONE ⇒
    patricialise_fused_clocked (n + m) kvs =
    patricialise_fused_clocked n kvs
Proof
  recInduct patricialise_fused_clocked_ind
  \\ rpt gen_tac \\ strip_tac
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
    \\ irule OPT_MMAP_cong
    \\ simp[]
    \\ gen_tac \\ strip_tac
    \\ `m + n - 1 = n - 1 + m` by ( Cases_on`n` \\ gs[] )
    \\ pop_assum SUBST_ALL_TAC
    \\ last_x_assum irule
    \\ gs[]
    \\ simp[Abbr`kvs`]
    \\ fs[CaseEq"option"]
    \\ qmatch_assum_abbrev_tac`OPT_MMAP f ls ≠ NONE`
    \\ `IS_SOME (OPT_MMAP f ls)` by (Cases_on`OPT_MMAP f ls` \\ gs[])
    \\ fs[OPT_MMAP_IS_SOME, EVERY_MAP, EVERY_MEM]
    \\ res_tac
    \\ strip_tac
    \\ fs[] )
  \\ simp[]
  \\ AP_THM_TAC
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ `m + n - 1 = n - 1 + m` by ( Cases_on`n` \\ gs[] )
  \\ pop_assum SUBST_ALL_TAC
  \\ first_x_assum irule
  \\ gs[]
  \\ reverse conj_tac >- rw[Abbr`kvs`]
  \\ strip_tac \\ fs[]
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
    \\ cheat (* use max of all the inductive clocks *) )
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

(* TODO: need to pull out the OPT_MMAP as first-order
val () = cv_auto_trans patricialise_fused_clocked_def;
*)

(*

Datatype:
  patricialsed_continuation =
    KExt (word8 list)
  | KBra (word8 list)
  | KRes (trie_node option)
  | KLst ((word8 list # word8 list) list list) ((trie_node option) list)
End

Definition patricialise_tr_def:
  patricialise_tr kvs ks =
  case kvs of
  | [] => KRes NONE :: ks
  | [(k,v)] => KRes (SOME $ Leaf k v) :: ks
  | _ =>
    let lcp = longest_common_prefix_of_list (MAP FST kvs) in
    if NULL lcp then let
      branches = GENLIST (make_branch kvs o n2w) 16;
      values = MAP SND (FILTER (NULL o FST) kvs);
      value = if NULL values then [] else HD values;
      bks = KBra value :: ks
    in
      KLst branches [] :: bks
    else
      patricialise_tr (drop_from_keys (LENGTH lcp) kvs)
        (KExt lcp :: ks)
Termination
  WF_REL_TAC`measure (SUM o (MAP $ LENGTH o FST) o FST)`
  \\ rpt gen_tac \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`MAP FST kvs`
  \\ rewrite_tac[drop_from_keys_map]
  \\ qmatch_goalsub_abbrev_tac`DROP n`
  \\ simp[MAP_MAP_o, o_DEF]
  \\ irule SUM_MAP_same_LESS
  \\ simp[]
  \\ Cases_on`n = 0` >- (unabbrev_all_tac \\ gs[])
  \\ gs[longest_common_prefix_of_list_CONS, NULL_EQ, Abbr`kvs`]
  \\ qmatch_goalsub_rename_tac`0 < LENGTH ls`
  \\ Cases_on`ls` \\ gs[]
End

Definition patricialise_k_def:
  patricialise_k ((KRes t)::(KExt lcp)::ks) =
    (KRes $ SOME $ Extension lcp t)::ks ∧
  patricialise_k ((KRes t)::(KLst bs acc)::ks) =
    KLst bs (t::acc) :: ks ∧
  patricialise_k ((KLst [] acc)::(KBra v)::ks) =
    (KRes $ SOME $ Branch (REVERSE acc) v)::ks ∧
  patricialise_k ((KLst (b::bs) acc)::ks) =
    patricialise_tr b (KLst bs acc :: ks) ∧
  patricialise_k _ = []
End

Definition isnt_KRes_sing_def:
  isnt_KRes_sing [(KRes _)] = F ∧
  isnt_KRes_sing _ = T
End

Definition dest_KRes_sing_def:
  dest_KRes_sing [(KRes t)] = t ∧
  dest_KRes_sing _ = NONE
End

Definition patricialise_loop_def:
  patricialise_loop 0 ks = NONE ∧
  patricialise_loop (SUC n) ks =
  if isnt_KRes_sing ks then
    patricialise_loop n (patricialise_k ks)
  else
    dest_KRes_sing ks
End

Definition patricialise_run_def:
  patricialise_run n kvs =
  patricialise_loop n (patricialise_tr kvs [])
End

(* why bother with this - just add a clock to patricialise_fused and use that *)

val () = cv_auto_trans patricialise_tr_def;
val () = cv_auto_trans patricialise_k_def;
val () = cv_auto_trans isnt_KRes_sing_def;
val () = cv_auto_trans dest_KRes_sing_def;
val () = cv_auto_trans patricialise_loop_def;
val () = cv_auto_trans patricialise_run_def;

*)

val _ = export_theory();
