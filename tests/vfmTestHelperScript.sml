open HolKernel boolLib bossLib Parse wordsLib dep_rewrite permLib
     pairTheory sortingTheory sumTheory wordsTheory
     vfmTypesTheory vfmExecutionTheory
     vfmStateTheory vfmContextTheory
     vfmOperationTheory vfmComputeTheory
     cv_transLib cv_typeTheory

val () = new_theory "vfmTestHelper";

Datatype:
  test_result
  = Passed
  | Failed
  | ExpectedException string
  | WrongNumTests
  | StateMismatch bytes32
  | LogsMismatch bytes32
  | OutOfFuel
End

Definition test_hashes_def:
  test_hashes fuel st (logs: event list) =
  case state_root_clocked fuel st
    of NONE => INR OutOfFuel
     | SOME sh => INL sh (* TODO: also rlp encode and hash the logs *)
End

val () = cv_auto_trans test_hashes_def;

Definition run_state_test_def:
  run_state_test fuel
    exec preState
    (expectException: string option)
    (stateHash: bytes32) (logsHash: bytes32) =
    case (
      case exec
        of NONE =>
            (if IS_NONE expectException then INR Failed
             else test_hashes fuel preState [])
         | SOME (result, postState) =>
            (if IS_SOME expectException then INR Failed
             else test_hashes fuel postState result.logs))
    of INR x => x
     | INL sh =>
         let computedHash = word_of_bytes T 0w sh in
         if computedHash = stateHash
         then Passed else StateMismatch computedHash
  (* TODO: check logs, check txbytes *)
End

val () = cv_auto_trans run_state_test_def;

(* TODO: remove below if unused, once new vfmTestLib is in use *)

Theorem unwind_lemma:
  (∃x y z. a = x ∧ b = y ∧ c = w ∧ d = z) ⇔ c = w
Proof
  rw[]
QED

Theorem unwind_lemma2:
  (∃x. a = b ∧ c = x) ⇔ a = b
Proof
  rw[]
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
