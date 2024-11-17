open HolKernel boolLib bossLib Parse
     listTheory rich_listTheory combinTheory
     arithmeticTheory sptreeTheory
     recursiveLengthPrefixTheory
     vfmTypesTheory

val _ = new_theory "merkle";

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
             SOME $ Branch (MAP patricialise branches) value
         else
           SOME $
           Extension lcp (patricialise (MAP (DROP (LENGTH lcp) ## I) kvs))
Proof
  recInduct patricialise_ind
  \\ rpt strip_tac
  >- EVAL_TAC
  >- EVAL_TAC
  \\ rewrite_tac[patricialise_def]
  \\ asm_rewrite_tac[]
  \\ simp_tac (std_ss ++ ETA_ss) [list_case_def]
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

val _ = export_theory();
