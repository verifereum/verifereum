open HolKernel boolLib bossLib Parse wordsLib dep_rewrite permLib
     pairTheory sortingTheory sumTheory wordsTheory
     vfmTypesTheory vfmExecutionTheory
     vfmStateTheory vfmContextTheory
     vfmOperationTheory vfmComputeTheory
     cv_transLib cv_typeTheory

val () = new_theory "vfmTestHelper";

Theorem run_transactions_with_fuel_sub:
  !ts n a rs qs m j.
  run_transactions_with_fuel n st c h b a rs ts = SOME (qs,d,m) /\ j <= m ==>
  m ≤ n ∧
  run_transactions_with_fuel (n - j) st c h b a rs ts = SOME (qs,d,m - j)
Proof
  Induct
  \\ simp[run_transactions_with_fuel_def]
  \\ qx_gen_tac`x` \\ rpt gen_tac
  \\ gvs[CaseEq"option", CaseEq"prod", PULL_EXISTS]
  \\ qx_genl_tac[`p`,`f`,`e`] \\ strip_tac
  \\ first_x_assum drule
  \\ disch_then(fn th => assume_tac th \\ qspec_then`0`mp_tac th)
  \\ impl_tac \\ simp[] \\ strip_tac
  \\ drule run_transaction_with_fuel_sub
  \\ strip_tac
  \\ drule run_transaction_with_fuel_add
  \\ disch_then(qspec_then`p - j`mp_tac)
  \\ simp[]
  \\ `p ≤ n`
  by (
    CCONTR_TAC
    \\ qhdtm_x_assum`run_transaction_with_fuel`mp_tac
    \\ qhdtm_x_assum`run_transaction_with_fuel`mp_tac
    \\ simp[run_transaction_with_fuel_def, run_with_fuel_def,
            run_create_def, CaseEq"bool", CaseEq"num", PULL_EXISTS,
            CaseEq"option", CaseEq"sum", CaseEq"prod"]
    \\ rpt gen_tac
    \\ strip_tac \\ gvs[]
    \\ qmatch_asmsub_abbrev_tac`run_with_fuel _ pp`
    \\ Cases_on`pp`
    \\ drule run_with_fuel_sub
    \\ gs[run_with_fuel_def, CaseEq"bool", CaseEq"num"]
    \\ strip_tac \\ gvs[]
    \\ metis_tac[NOT_ISL_ISR])
  \\ simp[]
QED

Theorem run_block_with_fuel_sub:
  run_block_with_fuel n c h a b = SOME (x, y, m) ==>
  run_block_with_fuel (n - m) c h a b = SOME (x, y, 0)
Proof
  rw[run_block_with_fuel_def, EXISTS_PROD]
  \\ drule run_transactions_with_fuel_sub
  \\ disch_then(qspec_then`m`mp_tac)
  \\ simp[]
QED

Theorem run_block_with_fuel_cv_sub:
  run_block_with_fuel n c h a b =
  to_option (to_pair f (to_pair g cv$c2n))
    (Pair (Num z) (Pair x (Pair y (Num m))))
  ⇒
  run_block_with_fuel (n - m) c h a b =
  to_option (to_pair f (to_pair g cv$c2n))
    (Pair (Num z) (Pair x (Pair y (Num 0))))
Proof
  rw[to_option_def, to_pair_def]
  \\ irule run_block_with_fuel_sub
  \\ rw[]
QED

Definition switch_def:
  switch x d [] = d ∧
  switch x d ((y,z)::ls) =
  if x = y then z else switch x d ls
End

Theorem COND_right_switch1:
  COND (x = b) y z = switch b z [(x,y)]
Proof
  rw[switch_def]
QED

Theorem switch1_switch:
  switch x (switch x d ls) [p] =
  switch x d (p::ls)
Proof
  Cases_on`p` \\ rw[switch_def]
QED

Theorem PERM_switch:
  !l1 l2. PERM l1 l2 ⇒ ALL_DISTINCT (MAP FST l1) ⇒
  switch b d l1 = switch b d l2
Proof
  ho_match_mp_tac PERM_STRONG_IND
  \\ rw[] \\ gs[]
  >- ( Cases_on`x` \\ rw[switch_def] )
  >- (
    Cases_on`x` \\ Cases_on`y`
    \\ rw[switch_def] \\ gs[] )
  \\ first_x_assum irule
  \\ metis_tac[PERM_MAP, ALL_DISTINCT_PERM]
QED

Theorem irreflexive_transitive_word_lo:
  irreflexive (word_lo:bytes32 -> bytes32 -> bool) ∧
  transitive  (word_lo:bytes32 -> bytes32 -> bool)
Proof
  rw[relationTheory.irreflexive_def, relationTheory.transitive_def]
  \\ irule WORD_LOWER_TRANS
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ first_x_assum ACCEPT_TAC
QED

val () = export_theory();
