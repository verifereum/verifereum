Theory merklePatriciaTrie
Ancestors
  arithmetic combin list rich_list pair
  sorting While words
  finite_map sptree
  longestCommonPrefix recursiveLengthPrefix
  vfmTypes
Libs
  cv_transLib
  blastLib wordsLib

(* TODO: move? *)

Theorem EXISTS_NUM_ADD:
  ∀P. (∃n:num. P n) ⇔ (∃a b. P (a + b))
Proof
  rw[EQ_IMP_THM]
  \\ TRY(qexistsl_tac[`0`,`n`] \\ rw[])
  \\ goal_assum drule
QED

Theorem list_size_sum_map_length:
  list_size f ls = SUM (MAP f ls) + LENGTH ls
Proof
  Induct_on`ls` \\ rw[]
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

Definition pointwise_sum2_def:
  pointwise_sum2 [] y = y ∧
  pointwise_sum2 x [] = x ∧
  pointwise_sum2 ((x:word8)::xs) (y::ys) =
    (x+y)::pointwise_sum2 xs ys
End

Definition pointwise_sum_def:
  pointwise_sum [] = [] ∧
  pointwise_sum (x::xs) =
  pointwise_sum2 x (pointwise_sum xs)
End

val () = cv_auto_trans pointwise_sum_def;

Theorem NULL_pointwise_sum2:
  ∀l1 l2. NULL $ pointwise_sum2 l1 l2 ⇔ NULL l1 ∧ NULL l2
Proof
  ho_match_mp_tac pointwise_sum2_ind
  \\ rw[pointwise_sum2_def]
QED

Theorem NULL_pointwise_sum:
  ∀ls. NULL $ pointwise_sum ls ⇔ EVERY NULL ls
Proof
  Induct
  \\ rw[pointwise_sum_def, NULL_pointwise_sum2]
QED

Definition patricialise_def:
  patricialise [] = NONE ∧
  patricialise [(k, v)] = SOME $ Leaf k v ∧
  patricialise kvs = let
    lcp = longest_common_prefix_of_list (MAP FST kvs)
  in
    if NULL lcp then
      let
        branches = GENLIST (make_branch kvs o n2w) 16;
        values = MAP SND $ FILTER (NULL o FST) kvs;
        value = pointwise_sum values
      in
        SOME $ Branch (MAP patricialise branches) value
    else
      SOME $
      Extension lcp (patricialise (MAP (DROP (LENGTH lcp) ## I) kvs))
Termination
  WF_REL_TAC `measure (list_size (LENGTH o FST))`
  \\ qmatch_goalsub_abbrev_tac `GENLIST _ nb`
  \\ simp[MEM_GENLIST, NULL_EQ, PULL_EXISTS]
  \\ reverse conj_tac
  \\ rpt gen_tac \\ qmatch_goalsub_abbrev_tac`longest_common_prefix_of_list ls`
  >- (
    rw[]
    \\ qspec_then`ls`mp_tac longest_common_prefix_of_list_thm
    \\ rw[NULL_EQ]
    \\ qmatch_goalsub_rename_tac`LENGTH h1`
    \\ `MEM h1 ls` by rw[Abbr`ls`]
    \\ qmatch_goalsub_abbrev_tac`LENGTH h1 - LENGTH lcp`
    \\ `IS_PREFIX h1 lcp` by metis_tac[]
    \\ `LENGTH lcp ≤ LENGTH h1` by metis_tac[IS_PREFIX_LENGTH]
    \\ qmatch_goalsub_rename_tac`LENGTH h2 + (_ + 2)`
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
  \\ gvs[EVERY_MEM, FORALL_PROD, NULL_EQ]
  \\ gvs[MEM_MAP, EXISTS_PROD]
  \\ first_assum $ irule_at Any
  \\ first_assum $ irule_at Any
  \\ first_assum $ irule_at Any
  \\ first_x_assum drule
  \\ CASE_TAC \\ rw[]
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

Theorem make_branch_PERM:
  PERM kvs1 kvs2 ==>
  PERM (make_branch kvs1 i) (make_branch kvs2 i)
Proof
  rw[make_branch_def]
  \\ irule PERM_MAP
  \\ irule PERM_FILTER
  \\ rw[]
QED

Theorem ALL_DISTINCT_MAP_FST_make_branch:
	ALL_DISTINCT (MAP FST ls) ⇒
  ALL_DISTINCT (MAP FST (make_branch ls x))
Proof
  rw[make_branch_def,MAP_MAP_o]
	\\ rw[GSYM MAP_MAP_o]
	\\ qmatch_goalsub_abbrev_tac`FILTER P`
	\\ `P = (λk. case k of [] => F | h::_ => x = h) o FST`
	by rw[Abbr`P`,FUN_EQ_THM]
	\\ pop_assum SUBST1_TAC
	\\ rw[GSYM FILTER_MAP]
	\\ irule ALL_DISTINCT_MAP_INJ
	\\ reverse conj_tac
	>- ( irule FILTER_ALL_DISTINCT \\ rw[] )
	\\ rw[MEM_FILTER]
	\\ gvs[EL_ALL_DISTINCT_EL_EQ]
	\\ gvs[MEM_EL, EL_MAP, Abbr`P`]
	\\ irule EQ_SYM
	\\ first_x_assum drule
	\\ disch_then $ irule o iffLR
	\\ rpt(qhdtm_x_assum`list_CASE`mp_tac)
	\\ CASE_TAC \\ CASE_TAC
	\\ gvs[]
QED

Theorem pointwise_sum2_nil[simp]:
  pointwise_sum2 x [] = x
Proof
  Induct_on`x` \\ rw[pointwise_sum2_def]
QED

Theorem pointwise_sum2_comm:
  ∀x y. pointwise_sum2 x y = pointwise_sum2 y x
Proof
  ho_match_mp_tac pointwise_sum2_ind
  \\ rw[pointwise_sum2_def]
QED

Theorem pointwise_sum2_assoc:
  ∀x y z. pointwise_sum2 x (pointwise_sum2 y z) =
          pointwise_sum2 (pointwise_sum2 x y) z
Proof
  ho_match_mp_tac pointwise_sum2_ind
  \\ rw[pointwise_sum2_def]
  \\ Cases_on`z` \\ gvs[pointwise_sum2_def]
QED

Theorem pointwise_sum_PERM:
  ∀l1 l2. PERM l1 l2 ⇒
  pointwise_sum l1 = pointwise_sum l2
Proof
  ho_match_mp_tac PERM_IND
  \\ rw[pointwise_sum_def]
  \\ Cases_on`l1` \\ gvs[GSYM NULL_EQ, pointwise_sum_def, NULL_pointwise_sum]
  \\ gvs[AC pointwise_sum2_assoc pointwise_sum2_comm]
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
  \\ BasicProvers.LET_ELIM_TAC
  \\ simp[]
  \\ reverse IF_CASES_TAC \\ simp[]
  >- (
    first_x_assum irule
    \\ simp[]
    \\ irule PERM_MAP
    \\ simp[] )
  \\ reverse conj_tac
  >- (
    simp[Abbr`value`, Abbr`value'`]
    \\ irule pointwise_sum_PERM
    \\ simp[Abbr`values`, Abbr`values'`]
    \\ qmatch_goalsub_abbrev_tac`FILTER P`
    \\ irule PERM_MAP
    \\ simp[PERM_FILTER])
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
val nibble_list_to_compact_pre_def = cv_trans_pre "nibble_list_to_compact_pre" nibble_list_to_compact_def;

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
       value = pointwise_sum values;
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
	\\ gvs[EVERY_MEM, FORALL_PROD, NULL_EQ]
	\\ gvs[MEM_MAP, EXISTS_PROD]
	\\ first_assum $ irule_at Any
	\\ first_assum $ irule_at Any
	\\ first_assum $ irule_at Any
	\\ first_x_assum drule
	\\ CASE_TAC \\ rw[]
End

Theorem patricialise_fused_thm:
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
QED

Definition patricialise_fused_list_def:
  patricialise_fused_list acc [] = REVERSE acc ∧
  patricialise_fused_list acc (x::xs) =
  patricialise_fused_list (patricialise_fused x :: acc) xs
End

Theorem patricialise_fused_list_thm:
  ∀ls acc. patricialise_fused_list acc ls =
  REVERSE acc ++ MAP patricialise_fused ls
Proof
  Induct \\ rw[patricialise_fused_list_def]
QED

Theorem patricialise_fused_list_map:
  MAP patricialise_fused = patricialise_fused_list []
Proof
  rw[patricialise_fused_list_thm, FUN_EQ_THM]
QED

Datatype:
  patricialise_fused_continuation
  = DoneK
  | MTEK (word8 list) patricialise_fused_continuation
  | MTBK (word8 list) patricialise_fused_continuation
  | AccK (rlp list) ((word8 list # word8 list) list list) patricialise_fused_continuation
  | Call1 ((word8 list # word8 list) list) patricialise_fused_continuation
  | App1 rlp patricialise_fused_continuation
  | Appn (rlp list) patricialise_fused_continuation
End

Definition patricialise_fused_cps_def:
  patricialise_fused_cps kvs c =
  case kvs of [] => App1 (encode_internal_node NONE) c
  | [(k,v)] => App1 (encode_internal_node (SOME (MTL k v))) c
  | _ => let lcp = longest_common_prefix_of_list (MAP FST kvs) in
    if NULL lcp then let
      branches = GENLIST (make_branch kvs o n2w) 16;
      values = MAP SND (FILTER (NULL o FST) kvs);
      value = pointwise_sum values;
    in AccK [] branches (MTBK value c)
    else let dkvs = drop_from_keys (LENGTH lcp) kvs
    in Call1 dkvs (MTEK lcp c)
End

val () = cv_auto_trans patricialise_fused_cps_def;

Definition patricialise_fused_list_cps_def:
  patricialise_fused_list_cps acc [] c =
    Appn (REVERSE acc) c ∧
  patricialise_fused_list_cps acc (x::xs) c =
    Call1 x (AccK acc xs c)
End

val () = cv_auto_trans patricialise_fused_list_cps_def;

Definition patricialise_fused_step_def:
  patricialise_fused_step (App1 subnode (MTEK lcp c)) =
    App1 (encode_internal_node (SOME (MTE lcp subnode))) c ∧
  patricialise_fused_step (App1 subnode (AccK acc xs c)) =
    patricialise_fused_list_cps (subnode::acc) xs c ∧
  patricialise_fused_step (Appn subnodes (MTBK value c)) =
    App1 (encode_internal_node (SOME (MTB subnodes value))) c ∧
  patricialise_fused_step (Call1 kvs c) =
    patricialise_fused_cps kvs c ∧
  patricialise_fused_step (AccK acc xs c) =
    patricialise_fused_list_cps acc xs c ∧
  patricialise_fused_step c = c
End

val () = cv_auto_trans patricialise_fused_step_def;

Theorem patricialise_fused_list_cps_thm:
  ∀acc ls.
    (∀x. MEM x ls ⇒
      ∀c. ∃n.
        FUNPOW patricialise_fused_step n (patricialise_fused_cps x c) =
	App1 (patricialise_fused x) c) ⇒
    ∃m. FUNPOW patricialise_fused_step m
          (patricialise_fused_list_cps acc ls c) =
	Appn (patricialise_fused_list acc ls) c
Proof
  Induct_on `ls`
  \\ rw[patricialise_fused_list_cps_def, patricialise_fused_list_def]
  >- (qexists_tac `0` \\ rw[])
  \\ Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM]
  \\ disj2_tac \\ simp[Once FUNPOW]
  \\ rw[patricialise_fused_step_def]
  \\ first_assum(qspec_then`h`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qspec_then`AccK acc ls c` $ qx_choose_then`m`strip_assume_tac)
  \\ Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM_ADD]
  \\ qexists_tac`m`
  \\ ONCE_REWRITE_TAC[ADD_COMM]
  \\ rw[FUNPOW_ADD]
  \\ Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM]
  \\ disj2_tac \\ simp[Once FUNPOW]
  \\ rw[patricialise_fused_step_def]
QED

Theorem patricialise_fused_cps_thm:
  ∀kvs c. ∃n.
  FUNPOW patricialise_fused_step n
    (patricialise_fused_cps kvs c) =
  App1 (patricialise_fused kvs) c
Proof
  ho_match_mp_tac patricialise_fused_ind
  \\ rpt strip_tac
  \\ rewrite_tac[Once patricialise_fused_cps_def]
  \\ CASE_TAC
  >- (
    rw[patricialise_fused_def]
    \\ qexists_tac `0` \\ rw[] )
  \\ CASE_TAC
  \\ CASE_TAC
  >- (
    rw[patricialise_fused_def]
    \\ qexists_tac `0` \\ rw[] )
  \\ qmatch_goalsub_abbrev_tac `MAP FST kvs`
  \\ qmatch_goalsub_abbrev_tac`LET _ lcp`
  \\ qmatch_asmsub_abbrev_tac`GENLIST _ nb`
  \\ gvs[]
  \\ IF_CASES_TAC
  >- (
    Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM]
    \\ disj2_tac \\ simp[Once FUNPOW]
    \\ simp[patricialise_fused_step_def]
    \\ gvs[]
    \\ rewrite_tac[Once patricialise_fused_def]
    \\ qmatch_goalsub_abbrev_tac`FUNPOW _ _ x`
    \\ CASE_TAC >- gvs[]
    \\ CASE_TAC \\ CASE_TAC >- gvs[]
    \\ qmatch_goalsub_abbrev_tac `MAP FST kvs`
    \\ qmatch_goalsub_abbrev_tac`GENLIST _ nbb`
    \\ gvs[]
    \\ qunabbrev_tac`x`
    \\ qmatch_goalsub_abbrev_tac`MTBK value` 
    \\ qmatch_goalsub_abbrev_tac`MAP _ ls`
    \\ qpat_x_assum`∀x. _`mp_tac
    \\ simp[Abbr`kvs`]
    \\ strip_tac
    \\ drule patricialise_fused_list_cps_thm
    \\ disch_then(qspecl_then[`MTBK value c`, `[]`]strip_assume_tac)
    \\ qexists_tac`SUC m`
    \\ rw[FUNPOW_SUC]
    \\ rw[patricialise_fused_step_def]
    \\ rw[patricialise_fused_list_map, ETA_AX] )
  \\ rewrite_tac[Once patricialise_fused_def]
  \\ qmatch_goalsub_abbrev_tac`GENLIST _ nbb`
  \\ gvs[Abbr`kvs`]
  \\ qmatch_goalsub_abbrev_tac`drop_from_keys ln kvs`
  \\ first_x_assum(qspec_then`MTEK lcp c`mp_tac)
  \\ disch_then(qx_choose_then`n`strip_assume_tac)
  \\ qexists_tac`1+n+1`
  \\ simp[Once FUNPOW_ADD]
  \\ simp[patricialise_fused_step_def]
  \\ rewrite_tac[Once ADD_COMM]
  \\ simp[Once FUNPOW_ADD]
  \\ simp[patricialise_fused_step_def]
QED

Definition not_App1_DoneK_def[simp]:
  not_App1_DoneK (App1 x DoneK) = F ∧
  not_App1_DoneK _ = T
End

Definition dest_App1_DoneK_def[simp]:
  dest_App1_DoneK (App1 x DoneK) = x ∧
  dest_App1_DoneK _ = RLPB []
End

val () = cv_auto_trans not_App1_DoneK_def;
val () = cv_auto_trans dest_App1_DoneK_def;

Definition patricialise_fused_cps_run_def:
  patricialise_fused_cps_run kvs =
  dest_App1_DoneK $
    WHILE not_App1_DoneK patricialise_fused_step $
      patricialise_fused_cps kvs DoneK
End

Theorem patricialise_fused_cps_run_thm:
  patricialise_fused_cps_run = patricialise_fused
Proof
  rw[FUN_EQ_THM, patricialise_fused_cps_run_def]
  \\ qspecl_then[`x`,`DoneK`]strip_assume_tac patricialise_fused_cps_thm
  \\ qmatch_goalsub_abbrev_tac`WHILE P f s`
  \\ `¬P (FUNPOW f n s)` by simp[Abbr`P`]
  \\ drule $ SRULE[PULL_EXISTS]WHILE_FUNPOW
  \\ disch_then SUBST_ALL_TAC
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- metis_tac[]
  \\ qx_gen_tac`m` \\ rw[]
  \\ `¬(n < m)` by metis_tac[]
  \\ `m ≤ n` by simp[]
  \\ `∀n. FUNPOW f (m + n) s = FUNPOW f m s`
  by (
    Induct \\ rw[]
    \\ rw[GSYM ADD_SUC]
    \\ rw[Once FUNPOW_SUC]
    \\ qmatch_goalsub_abbrev_tac`f r`
    \\ Cases_on`r` \\ gvs[Abbr`P`,Abbr`f`]
    \\ Cases_on`p` \\ gvs[patricialise_fused_step_def] )
  \\ gvs[LESS_EQ_EXISTS]
QED

Definition patricialise_fused_cps_loop_def:
  patricialise_fused_cps_loop =
  WHILE not_App1_DoneK patricialise_fused_step
End

Theorem patricialise_fused_cps_loop_eqn:
  patricialise_fused_cps_loop x =
  if not_App1_DoneK x then
    patricialise_fused_cps_loop $
      patricialise_fused_step x
  else x
Proof
  rw[Once patricialise_fused_cps_loop_def]
  \\ rw[Once WHILE]
  \\ rw[GSYM patricialise_fused_cps_loop_def]
QED

val patricialise_fused_cps_loop_pre_def =
  cv_auto_trans_pre "patricialise_fused_cps_loop_pre"
    patricialise_fused_cps_loop_eqn;

val patricialise_fused_cps_run_pre_def =
  cv_auto_trans_pre "patricialise_fused_cps_run_pre" $
  SRULE [GSYM patricialise_fused_cps_loop_def]
    patricialise_fused_cps_run_def;

Theorem patricialise_fused_cps_run_pre[cv_pre]:
  patricialise_fused_cps_run_pre kvs
Proof
  rw[patricialise_fused_cps_run_pre_def]
  \\ qspecl_then[`kvs`,`DoneK`]strip_assume_tac patricialise_fused_cps_thm
  \\ pop_assum mp_tac
  \\ qmatch_goalsub_rename_tac`FUNPOW _ _ s`
  \\ qid_spec_tac`s`
  \\ Induct_on`n` \\ rw[]
  \\ rw[Once patricialise_fused_cps_loop_pre_def]
  \\ first_x_assum irule
  \\ gs[Once FUNPOW]
QED

val () =
  cv_trans $
  SRULE[FUN_EQ_THM] $ GSYM
  patricialise_fused_cps_run_thm;

(* TODO: move
(* also move cv_LEN_add! *)
Theorem not_cv_NULL_cv_LENGTH_pos:
  ¬cv$c2b (cv_NULL v) ⇒
  ∃n. cv_LENGTH v = Num n ∧ 0 < n
Proof
  Cases_on `v` \\ rw[cv_NULL_def, cv_LENGTH_def, Once cv_LEN_def]
  \\ rw[Once keccakTheory.cv_LEN_add]
  \\ qmatch_goalsub_rename_tac `cv_add _ cv`
  \\ Cases_on`cv` \\ rw[cvTheory.cv_add_def]
QED

Theorem cv_size_cv_DROP_leq:
  ∀n v. cv_size (cv_DROP n v) ≤ cv_size v
Proof
  Induct_on `v` \\ rw[]
  \\ rw[Once cv_DROP_def]
  \\ irule LESS_EQ_TRANS
  \\ qmatch_goalsub_rename_tac `cv_DROP _ v2`
  \\ qexists_tac `cv_size v2`
  \\ simp[]
QED

Theorem cv_size_cv_DROP_less:
  ∀m. 0 < m ∧ cv$c2b (cv_ispair v) ⇒ cv_size (cv_DROP (Num m) v) < cv_size v
Proof
  Induct_on`v`
  \\ rw[Once cv_DROP_def]
  \\ qmatch_goalsub_rename_tac `cv_DROP _ v2`
  \\ ntac 2 (pop_assum mp_tac)
  \\ Cases_on `v2` \\ rw[Once cv_DROP_def]
  \\ rw[Once cv_DROP_def]
  \\ gvs[]
  \\ pop_assum mp_tac \\ rw[]
  \\ first_x_assum(qspec_then`m-1`mp_tac)
  \\ simp[]
QED
-- *)

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
