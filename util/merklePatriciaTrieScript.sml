open HolKernel boolLib bossLib Parse
     listTheory rich_listTheory combinTheory sortingTheory wordsTheory
     optionTheory arithmeticTheory finite_mapTheory sptreeTheory
     byteTheory pairTheory alistTheory numposrepTheory wordsLib blastLib
     recursiveLengthPrefixTheory vfmTypesTheory
     cv_transLib cv_typeLib cv_typeTheory cv_stdTheory

val _ = new_theory "merklePatriciaTrie";

(* TODO: move? *)

Theorem list_size_sum_map_length:
  list_size f ls = SUM (MAP f ls) + LENGTH ls
Proof
  Induct_on`ls` \\ rw[]
QED

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

Theorem longest_common_prefix_is_nil:
  longest_common_prefix x y = [] ⇔
  (x = [] ∨ y = [] ∨ HD x ≠ HD y)
Proof
  rw[EQ_IMP_THM]
  \\ Cases_on `x` \\ gvs[]
  \\ Cases_on `y` \\ gvs[]
  \\ gvs[longest_common_prefix_def]
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

Theorem longest_common_prefix_of_list_is_nil:
  ∀ls. longest_common_prefix_of_list ls = [] ⇔
  (ls = [] ∨
   ∃x y. MEM x ls ∧ MEM y ls ∧ longest_common_prefix x y = [])
Proof
  Induct_on`ls` \\ rw[]
  >- gvs[longest_common_prefix_of_list_def]
  \\ rw[longest_common_prefix_of_list_CONS]
  \\ gvs[NULL_EQ, longest_common_prefix_is_nil]
  \\ Cases_on`longest_common_prefix_of_list ls` \\ gvs[]
  >- metis_tac[]
  \\ Cases_on`h` \\ gvs[]
  >- metis_tac[]
  \\ qmatch_goalsub_rename_tac`h1 = h2 ⇒ _`
  \\ qspec_then`ls`mp_tac longest_common_prefix_of_list_thm
  \\ rw[NULL_EQ]
  \\ Cases_on`h1 ≠ h2` \\ gvs[]
  >- (
    Cases_on`ls` \\ gvs[]
    \\ qmatch_goalsub_rename_tac`h1::t1`
    \\ qexistsl_tac [`h1::t1`,`h`]
    \\ simp[]
    \\ Cases_on`h` \\ gvs[]
    \\ fsrw_tac[DNF_ss][] \\ rw[] )
  \\ rw[EQ_IMP_THM]
  >- metis_tac[]
  \\ TRY(first_x_assum drule \\ CASE_TAC \\ rw[] \\ NO_TAC)
  \\ metis_tac[]
QED

Theorem ALL_DISTINCT_MAP_DROP_LESS:
  !ls.
    n <= m /\
    ALL_DISTINCT (MAP (DROP m) ls) ==>
    ALL_DISTINCT (MAP (DROP n) ls)
Proof
  Induct \\ rw[] \\ fs[MEM_MAP, PULL_EXISTS]
  \\ rw[] \\ first_x_assum irule
  \\ full_simp_tac(srw_ss() ++ numSimps.ARITH_ss)
     [LIST_EQ_REWRITE, EL_DROP, LENGTH_DROP, LESS_EQ_EXISTS]
QED

Theorem ALL_DISTINCT_DROP_LENGTH_lcp:
  ∀ls. ALL_DISTINCT ls ⇒
       ALL_DISTINCT (MAP (DROP (LENGTH $ longest_common_prefix_of_list ls)) ls)
Proof
  Induct \\ reverse(rw[])
  \\ gs[longest_common_prefix_of_list_CONS]
  \\ rw[NULL_EQ] \\ gvs[MEM_MAP]
  \\ qmatch_goalsub_abbrev_tac`longest_common_prefix x y`
  \\ qspecl_then[`x`,`y`]mp_tac longest_common_prefix_thm
  \\ strip_tac
  >- (
    irule ALL_DISTINCT_MAP_DROP_LESS
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[IS_PREFIX_LENGTH] )
  \\ qx_gen_tac`z` \\ strip_tac
  \\ strip_tac
  \\ drule $ cj 1 longest_common_prefix_of_list_thm
  \\ simp[] \\ strip_tac
  \\ `x = z` suffices_by (strip_tac \\ gs[])
  \\ qmatch_asmsub_abbrev_tac`LENGTH lcp`
  \\ gvs[IS_PREFIX_APPEND, PULL_EXISTS, DROP_APPEND]
  \\ qmatch_goalsub_abbrev_tac`DROP n`
  \\ `n = 0` suffices_by simp[]
  \\ simp[Abbr`n`]
QED

Datatype:
  trie_node =
    Leaf      (byte list) (byte list)
  | Extension (byte list) (trie_node option)
  | Branch    (trie_node option list) (byte list)
End

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
      \\ simp[Abbr`f`, Abbr`g`, LENGTH_TL_LE, EXISTS_MEM]
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
    \\ drule PERM_NULL_EQ
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

val () = cv_auto_trans nibble_list_to_bytes_def;
val nibble_list_to_compact_pre_def = cv_trans_pre nibble_list_to_compact_def;

Theorem nibble_list_to_compact_pre[cv_pre]:
  nibble_list_to_compact_pre x y
Proof
  rw[nibble_list_to_compact_pre_def]
  \\ strip_tac \\ gs[]
QED

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
    else RLPB $ Keccak_256_w64 encoded
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

Definition trie_root_def:
  trie_root t = let
    root_node = encode_internal_node t;
    encoded = rlp_encode root_node
  in
    if LENGTH encoded < 32 then
      Keccak_256_w64 encoded
    else
      dest_RLPB root_node
End

Theorem make_branch_eta[local]:
  make_branch kvs nb =
  MAP (λp. (TL (FST p), SND p)) $ FILTER (λkv. [nb] ≼ FST kv) kvs
Proof
  rw[make_branch_def]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ rw[FUN_EQ_THM, FORALL_PROD, PAIR_MAP]
QED

val () = make_branch_eta |> cv_auto_trans;
val () = longest_common_prefix_of_list_def |> cv_auto_trans;

Definition patricialise_fused_def:
  patricialise_fused kvs =
  (case kvs of
   | [] => encode_internal_node NONE
   | [(k,v)] => encode_internal_node $ SOME $ MTL k v
   | _ => let lcp = longest_common_prefix_of_list (MAP FST kvs) in
     if NULL lcp then let
       branches = GENLIST (make_branch kvs o n2w) 16;
       values = MAP SND (FILTER (NULL o FST) kvs);
       value = if NULL values then [] else HD values;
       subnodes = MAP patricialise_fused branches;
       in encode_internal_node $ SOME $ MTB subnodes value
     else let
       dkvs = drop_from_keys (LENGTH lcp) kvs;
       subnode = patricialise_fused dkvs
       in encode_internal_node $ SOME $ MTE lcp subnode)
Termination
  WF_REL_TAC `measure (list_size (LENGTH o FST))`
  \\ qmatch_goalsub_abbrev_tac `GENLIST _ nb`
  \\ simp[MEM_GENLIST, NULL_EQ, PULL_EXISTS]
  \\ reverse conj_tac
  \\ rpt gen_tac \\ qmatch_goalsub_abbrev_tac`longest_common_prefix_of_list ls`
  >- (
    rw[drop_from_keys_map]
    \\ qspec_then`ls`mp_tac longest_common_prefix_of_list_thm
    \\ rw[NULL_EQ]
    \\ qmatch_goalsub_rename_tac`LENGTH h1`
    \\ `MEM h1 ls` by rw[Abbr`ls`]
    \\ qmatch_goalsub_abbrev_tac`LENGTH h1 - LENGTH lcp`
    \\ `IS_PREFIX h1 lcp` by metis_tac[]
    \\ `LENGTH lcp ≤ LENGTH h1` by metis_tac[IS_PREFIX_LENGTH]
    \\ qmatch_goalsub_rename_tac`LENGTH h2 - _ + list_size _ _`
    \\ `MEM h2 ls` by rw[Abbr`ls`]
    \\ `IS_PREFIX h2 lcp` by metis_tac[]
    \\ `LENGTH lcp ≤ LENGTH h2` by metis_tac[IS_PREFIX_LENGTH]
    \\ simp[list_size_sum_map_length]
    \\ qmatch_goalsub_abbrev_tac`SUM l1`
    \\ qmatch_goalsub_abbrev_tac`lhs < _`
    \\ qmatch_goalsub_abbrev_tac`SUM l2`
    \\ `SUM l1 <= SUM l2`
    by (
      rw[Abbr`l1`,Abbr`l2`]
      \\ irule SUM_MAP_same_LE
      \\ rw[EVERY_MEM] )
    \\ `0 < LENGTH lcp` by ( CCONTR_TAC \\ gvs[] )
    \\ rw[Abbr`lhs`] )
  \\ rw[longest_common_prefix_of_list_is_nil]
  \\ qmatch_goalsub_abbrev_tac`make_branch ps`
  \\ `ls = MAP FST ps` by rw[Abbr`ps`, Abbr`ls`]
  \\ qunabbrev_tac`ls`
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[make_branch_def, MAP_MAP_o, o_DEF]
  \\ rw[list_size_sum_map_length]
  \\ rw[make_branch_def]
  \\ qmatch_goalsub_abbrev_tac`lfp + smp < l1 + (l2 + (l3 + (sm + 2)))`
  \\ `l1 + l2 + sm = SUM (MAP (LENGTH o FST) ps)` by rw[Abbr`ps`,Abbr`sm`,o_DEF]
  \\ `l3 + 2 = LENGTH ps` by rw[Abbr`l3`,Abbr`ps`]
	\\ qmatch_asmsub_abbrev_tac`FILTER P`
	\\ qmatch_asmsub_abbrev_tac`MAP f1 (FILTER _ _)`
	\\ qmatch_asmsub_abbrev_tac`MAP f2 ps`
	\\ `SUM (MAP f2 (FILTER P ps)) ≤ SUM (MAP f2 ps)`
	by (
	  irule SUM_SUBLIST
		\\ irule MAP_SUBLIST
		\\ rw[FILTER_sublist] )
  \\ `smp ≤ SUM (MAP (LENGTH o FST) ps)` by (
    rw[Abbr`smp`, MAP_MAP_o, o_DEF]
    \\ irule LESS_EQ_TRANS
		\\ first_assum $ irule_at Any
    \\ irule SUM_MAP_same_LE
    \\ simp[Abbr`f1`,Abbr`f2`,EVERY_MEM,MEM_FILTER,Abbr`P`]
    \\ Cases \\ simp[] \\ CASE_TAC \\ rw[] )
	\\ Cases_on`lfp < LENGTH ps` >- gvs[]
	\\ `lfp ≤ LENGTH ps` by simp[Abbr`lfp`, LENGTH_FILTER_LEQ]
	\\ `lfp = LENGTH ps` by gvs[]
	\\ `EVERY P ps`
	by (
	  spose_not_then strip_assume_tac
		\\ fs[]
		\\ drule LENGTH_FILTER_LESS
		\\ gvs[] )
	\\ `smp < SUM (MAP (LENGTH o FST) ps)` suffices_by gvs[]
	\\ rw[Abbr`smp`, MAP_MAP_o, o_DEF]
	\\ irule LESS_LESS_EQ_TRANS
	\\ first_assum $ irule_at Any
	\\ irule SUM_MAP_same_LESS
	\\ simp[Abbr`f1`,Abbr`f2`,EVERY_MEM,MEM_FILTER,Abbr`P`,EXISTS_MEM]
	\\ simp[FORALL_PROD, EXISTS_PROD]
	\\ conj_tac
	>- ( Cases \\ simp[] \\ CASE_TAC \\ rw[] )
	\\ gvs[EVERY_MEM, FORALL_PROD, NULL_EQ]
	\\ gvs[MEM_MAP, EXISTS_PROD]
	\\ first_assum $ irule_at Any
	\\ first_assum $ irule_at Any
	\\ first_assum $ irule_at Any
	\\ first_x_assum drule
	\\ CASE_TAC \\ rw[]
End

Theorem patricialise_fused_thm:
  ALL_DISTINCT (MAP FST kvs) ⇒
  patricialise_fused kvs
    = encode_internal_node $ OPTION_MAP encode_trie_node $ patricialise kvs
Proof
  qid_spec_tac`kvs`
  \\ ho_match_mp_tac patricialise_ind
  \\ conj_tac
  >- rw[patricialise_def, patricialise_fused_def]
  \\ conj_tac
  >- rw[patricialise_def, patricialise_fused_def, encode_trie_node_def]
  \\ rpt gen_tac \\ strip_tac
  \\ strip_tac
  \\ rewrite_tac[Once patricialise_fused_def]
  \\ qmatch_goalsub_abbrev_tac`GENLIST _ nb`
  \\ rewrite_tac[list_case_def]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rewrite_tac[list_case_def]
  \\ BasicProvers.LET_ELIM_TAC
  \\ rewrite_tac[Once patricialise_def]
  \\ qmatch_goalsub_abbrev_tac`MAP FST kvs`
  \\ BasicProvers.LET_ELIM_TAC
  \\ simp[Abbr`lcp'`,Abbr`values'`]
  \\ reverse IF_CASES_TAC
  \\ simp[encode_trie_node_def]
  \\ AP_TERM_TAC \\ simp[]
  >- (
    gvs[ETA_AX, drop_from_keys_map]
    \\ first_x_assum irule
    \\ qunabbrev_tac`dkvs`
    \\ qunabbrev_tac`lcp`
    \\ simp[MAP_MAP_o]
    \\ simp[GSYM MAP_MAP_o]
    \\ irule ALL_DISTINCT_DROP_LENGTH_lcp
    \\ rw[] )
  \\ qunabbrev_tac`branches'`
  \\ gvs[ETA_AX]
  \\ simp[Abbr`subnodes`]
  \\ simp[MAP_MAP_o]
  \\ rw[MAP_EQ_f]
  \\ first_x_assum irule
  \\ gs[]
  \\ gvs[Abbr`branches`, MEM_GENLIST]
  \\ rw[make_branch_def]
  \\ rw[MAP_MAP_o]
  \\ qmatch_goalsub_abbrev_tac`FILTER P`
  \\ `ALL_DISTINCT (MAP FST (FILTER P kvs))`
  by (
    irule sublist_ALL_DISTINCT
    \\ first_assum $ irule_at Any
    \\ irule MAP_SUBLIST
    \\ rw[FILTER_sublist] )
  \\ rw[GSYM MAP_MAP_o]
  \\ irule ALL_DISTINCT_MAP_INJ
  \\ rw[MEM_MAP, MEM_FILTER, Abbr`P`]
  \\ rpt(qpat_x_assum`list_case _ _ _`mp_tac)
  \\ CASE_TAC \\ CASE_TAC
  \\ rw[] \\ gvs[]
QED

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
    \\ `EVERY (λa. ALL_DISTINCT (MAP FST a)) bs`
    by (
      rw[Abbr`bs`, EVERY_GENLIST, make_branch_def, o_DEF, MAP_MAP_o]
      \\ qpat_x_assum`ALL_DISTINCT _`mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ Induct_on`kvs` \\ rw[]
      \\ gs[MEM_MAP, MEM_FILTER]
      \\ Cases_on`h` \\ Cases \\ gs[]
      \\ qmatch_goalsub_rename_tac`TL a = TL b`
      \\ Cases_on`a` \\ Cases_on`b` \\ gs[] )
    \\ fs[EVERY_MEM]
    \\ simp[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
    \\ simp[RIGHT_EXISTS_IMP_THM]
    \\ disch_then(qx_choose_then`f`strip_assume_tac)
    \\ `subnodes = REVERSE [] ++ subnodes` by simp[]
    \\ pop_assum SUBST1_TAC
    \\ qexists_tac`SUM (MAP f bs) + LENGTH bs + 1`
    \\ irule patricialise_fused_clocked_mmap_thm
    \\ conj_tac >- simp[]
    \\ simp[GSYM GENLIST_EL_MAP]
    \\ simp[Abbr`subnodes`]
    \\ simp[GENLIST_FUN_EQ, EL_MAP]
    \\ gs[MEM_EL, PULL_EXISTS, ETA_AX]
    \\ qx_gen_tac`n` \\ strip_tac
    \\ first_x_assum drule
    \\ strip_tac
    \\ qmatch_assum_abbrev_tac`x = SOME _`
    \\ `x ≠ NONE` by (Cases_on`x` \\ fs[])
    \\ qunabbrev_tac`x`
    \\ drule (cj 1 patricialise_fused_clocked_add)
    \\ qmatch_goalsub_abbrev_tac`_ m _ = _`
    \\ `f (EL n bs) ≤ m` by (
      qunabbrev_tac`m`
      \\ qmatch_goalsub_abbrev_tac`x + y - n`
      \\ irule LESS_EQ_TRANS
      \\ qexists_tac`y` \\ simp[]
      \\ qunabbrev_tac`y`
      \\ qunabbrev_tac`x`
      \\ simp[GENLIST_EL_MAP]
      \\ irule SUM_MAP_MEM_bound
      \\ metis_tac[MEM_EL] )
    \\ drule (LESS_EQ_EXISTS |> SPEC_ALL |> iffLR)
    \\ metis_tac[])
  \\ gs[GSYM drop_from_keys_map, CaseEq"option"]
  \\ simp[encode_trie_node_def]
  \\ qmatch_goalsub_abbrev_tac`MTE lcp subnode`
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`subnode` \\ simp[]
  \\ qunabbrev_tac`subnode`
  \\ simp[ETA_AX]
  \\ first_x_assum irule
  \\ simp[drop_from_keys_map]
  \\ simp[MAP_MAP_o, o_DEF]
  \\ qmatch_goalsub_abbrev_tac`_ ls`
  \\ `ls = MAP (DROP $ LENGTH lcp) (MAP FST kvs)`
  by simp[Abbr`ls`, MAP_MAP_o, o_DEF]
  \\ pop_assum SUBST1_TAC
  \\ qunabbrev_tac`lcp`
  \\ irule ALL_DISTINCT_DROP_LENGTH_lcp
  \\ simp[]
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
    if LENGTH e < 32 then Keccak_256_w64 e else dest_RLPB r
End

val () = cv_auto_trans trie_root_clocked_def;

(*

(* empty state test *)

val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"``;

val root = cv_eval``state_root_clocked 100 empty_accounts``

(* account encoding test *)

val account = ``
  <| balance := 0x0ba1a9ce0ba1a9ce;
       code := [];
       nonce := 0;
       storage := empty_storage |>
``

val encoded = cv_eval``encode_account_clocked 100 ^account``

val correct_encoding = cv_eval``REVERSE $ hex_to_rev_bytes []
  "f84c80880ba1a9ce0ba1a9cea056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"``;

val true = aconv (rand(concl encoded)) (rand(concl correct_encoding))

(* single account state test *)

val addr = ``0xa94f5374fce5edbc8e2a8697c15331677e6ebf0bw : address``

val state = ``
  update_account ^addr ^account empty_accounts
``;

val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "c7a2369be883c297b5252d0006157561eae7f2a0f9b34b6b94e618a37731b043"``;

val root = cv_eval``state_root_clocked 100 ^state``

val true = aconv (rand(rand(concl root))) (rand(concl correct_root))

(*
val kvs = cv_eval``state_kvs 100
  (toAList (insert (w2n ^addr) ^account LN)) []``

val pres = cv_eval``patricialise_fused_clocked 100 ^(rhs(concl kvs))``

cv_eval``SND $ HD $ ^(rhs(concl kvs))``

val correct_key_nibbles = cv_eval``REVERSE $ hex_to_rev_bytes []
  "00030600010406020009030b050904050d010607060d0f0009030404060709000f0d03010b02000e070b01020a020e080e050e00090d0006080100090601060b"``

val key_nibbles = cv_eval``account_key ^addr``

val compact_key = cv_eval``nibble_list_to_compact ^(rhs(concl key_nibbles)) T``
val correct_compact_key = cv_eval``REVERSE $ hex_to_rev_bytes []
  "2003601462093b5945d1676df093446790fd31b20e7b12a2e8e5e09d068109616b"``

val preencoded_leaf = cv_eval``
  encode_internal_node_unencoded (SOME (MTL ^(rhs(concl key_nibbles))
    ^(rhs(concl encoded))))``;
val encoded_leaf = cv_eval`` rlp_encode $ ^(rhs(concl preencoded_leaf))``

cv_eval``rlp_bytes $ dest_RLPB $ EL 1 $ ^(rand(rhs(concl preencoded_leaf)))``

val correct_encoded_leaf = cv_eval``REVERSE $ hex_to_rev_bytes []
    "f872a12003601462093b5945d1676df093446790fd31b20e7b12a2e8e5e09d068109616bb84ef84c80880ba1a9ce0ba1a9cea056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"``;

cv_eval``word_to_bytes (0xa94f5374fce5edbc8e2a8697c15331677e6ebf0bw:address) T``
cv_eval``REVERSE $ hex_to_rev_bytes [] "a94f5374fce5edbc8e2a8697c15331677e6ebf0bw"``
*)

(* non-empty storage *)
val storage = ``update_storage 0w 3w empty_storage``
val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "db913528a1ccbc4403ae18eb823863b107a1c01c008f0ebccbd896e03c5f9792"``;
val root = cv_eval``storage_root_clocked 20 ^storage``

(*
val key = cv_eval``storage_key 0``
val correct_key = cv_eval``REVERSE $ hex_to_rev_bytes []
  "0209000d0e0c0d090504080b06020a080d06000304050a0908080308060f0c08040b0a060b0c09050408040000080f060306020f09030106000e0f030e050603"``;
*)

(* more accounts *)

val state = ``
  update_account ^addr ^account $
  update_account 0xccccccccccccccccccccccccccccccccccccccccw
  <| balance := 0x0ba1a9ce0ba1a9ce;
     nonce := 0;
     code := REVERSE $ hex_to_rev_bytes []
       "600060006000600060006004356110000162fffffff100";
     storage := empty_storage |> $
  update_account 0x0000000000000000000000000000000000001001w
  <| balance := 0x0ba1a9;
     code := REVERSE $ hex_to_rev_bytes []
       "60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500";
     nonce := 1;
     storage := update_storage 0x00w 0x03w empty_storage |>
  empty_accounts
``;

val root = cv_eval``state_root_clocked 100 ^state``;

val correct_root = cv_eval``REVERSE $ hex_to_rev_bytes []
  "aa00aae8b6c3ef96d899938796cad78006ab07bf8a7dc9cf8e1ef52598c58cb4"``;

val true = aconv (rand(rand(concl root))) (rand(concl correct_root))

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
