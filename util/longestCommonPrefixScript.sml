Theory longestCommonPrefix
Ancestors
  arithmetic list rich_list sorting

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
