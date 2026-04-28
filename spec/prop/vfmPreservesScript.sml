(*
 * Generic monadic predicate framework.
 *
 * Provides two parameterised predicates:
 *   - preserves R m: for any starting state s and result (r, s'),
 *     the state relation R s s' holds. No precondition on s.
 *   - preserves_when pre R m: as above, but only when the input
 *     state satisfies the precondition pre.
 *
 * Both are closed under the standard monad combinators (bind,
 * ignore_bind, handle, cond, case). Composition lemmas are proved
 * once here and instantiated for each specific R in downstream
 * theories via preserves_mono / preserves_when_mono_R.
 *
 * For bind / handle composition, transitivity of R is required as a
 * side-condition because bind chains two computations: if
 * g s = (INL x, s') and f x s' = (r, s'') then R s s' and R s' s''
 * give R s s'' by transitivity. All state relations used in practice
 * (equality, subset, same_frame_rel, etc.) are transitive.
 *
 * Companion theories define specific state relations (rollback_rel,
 * storage_rel, cp_rel, etc.) and prove that existing predicates are
 * equivalent to preserves / preserves_when instances. Implication
 * bridges between state relations then give bridges between
 * predicates for free via preserves_mono.
 *)
Theory vfmPreserves
Ancestors
  vfmExecution
Libs
  BasicProvers

(* ================================================================== *)
(* Definitions                                                        *)
(* ================================================================== *)

Definition preserves_def:
  preserves (R: execution_state -> execution_state -> bool)
            (m: execution_state -> (α + exception option) # execution_state) ⇔
    ∀s r s'. m s = (r, s') ⇒ R s s'
End

Definition preserves_when_def:
  preserves_when (pre: execution_state -> bool)
                 (R: execution_state -> execution_state -> bool)
                 (m: execution_state -> (α + exception option) # execution_state) ⇔
    ∀s r s'. m s = (r, s') ∧ pre s ⇒ R s s'
End

(* ================================================================== *)
(* Implication bridges                                                *)
(* ================================================================== *)

Theorem preserves_mono:
  (∀s s'. R1 s s' ⇒ R2 s s') ⇒
  preserves R1 m ⇒ preserves R2 m
Proof
  rw[preserves_def] >> metis_tac[]
QED

Theorem preserves_when_mono_R:
  (∀s s'. R1 s s' ⇒ R2 s s') ⇒
  preserves_when pre R1 m ⇒ preserves_when pre R2 m
Proof
  rw[preserves_when_def] >> metis_tac[]
QED

Theorem preserves_when_mono_pre:
  (∀s. pre2 s ⇒ pre1 s) ⇒
  preserves_when pre1 R m ⇒ preserves_when pre2 R m
Proof
  rw[preserves_when_def] >> metis_tac[]
QED

Theorem preserves_imp_preserves_when:
  preserves R m ⇒ preserves_when pre R m
Proof
  rw[preserves_when_def, preserves_def]
QED

Theorem preserves_when_T_imp_preserves:
  preserves_when (K T) R m ⇒ preserves R m
Proof
  rw[preserves_def, preserves_when_def]
QED

Theorem preserves_eq_preserves_when_T:
  preserves R m ⇔ preserves_when (K T) R m
Proof
  metis_tac[preserves_imp_preserves_when, preserves_when_T_imp_preserves]
QED

(* Conjunction: if m preserves R1 and R2, it preserves (R1 ∧ R2). *)
Theorem preserves_conj:
  preserves R1 m ∧ preserves R2 m ⇒
  preserves (λs s'. R1 s s' ∧ R2 s s') m
Proof
  rw[preserves_def] >> metis_tac[]
QED

Theorem preserves_conj_elim1:
  preserves (λs s'. R1 s s' ∧ R2 s s') m ⇒ preserves R1 m
Proof
  rw[preserves_def] >> metis_tac[]
QED

Theorem preserves_conj_elim2:
  preserves (λs s'. R1 s s' ∧ R2 s s') m ⇒ preserves R2 m
Proof
  rw[preserves_def] >> metis_tac[]
QED

(* ================================================================== *)
(* Composition lemmas for preserves                                   *)
(* ================================================================== *)

Theorem preserves_return:
  (∀s. R s s) ⇒ preserves R (return x)
Proof
  rw[preserves_def, return_def]
QED

Theorem preserves_fail:
  (∀s. R s s) ⇒ preserves R (fail e)
Proof
  rw[preserves_def, fail_def]
QED

Theorem preserves_reraise:
  (∀s. R s s) ⇒ preserves R (reraise e)
Proof
  rw[preserves_def, reraise_def]
QED

Theorem preserves_assert:
  (∀s. R s s) ⇒ preserves R (assert b e)
Proof
  rw[preserves_def, assert_def, return_def, fail_def]
QED

Theorem preserves_bind:
  preserves R g ∧ (∀x. preserves R (f x)) ∧
  (∀s1 s2 s3. R s1 s2 ∧ R s2 s3 ⇒ R s1 s3)
  ⇒ preserves R (bind g f)
Proof
  rw[preserves_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> last_x_assum drule >> rw[]
  >> last_x_assum drule >> rw[]
  >> metis_tac[]
QED

Theorem preserves_ignore_bind:
  preserves R g ∧ preserves R f ∧
  (∀s1 s2 s3. R s1 s2 ∧ R s2 s3 ⇒ R s1 s3)
  ⇒ preserves R (ignore_bind g f)
Proof
  rw[ignore_bind_def] >> irule preserves_bind >> rw[] >> metis_tac[]
QED

Theorem preserves_handle:
  preserves R f ∧ (∀e. preserves R (h e)) ∧
  (∀s1 s2 s3. R s1 s2 ∧ R s2 s3 ⇒ R s1 s3)
  ⇒ preserves R (handle f h)
Proof
  rw[preserves_def, handle_def]
  >> gvs[AllCaseEqs()]
  >> last_x_assum drule >> rw[]
  >> last_x_assum drule >> rw[]
  >> metis_tac[]
QED

Theorem preserves_cond:
  preserves R m1 ∧ preserves R m2 ⇒
  preserves R (if b then m1 else m2)
Proof
  rw[]
QED

Theorem preserves_case_option:
  preserves R m_none ∧ (∀x. preserves R (m_some x)) ⇒
  preserves R (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem preserves_case_sum:
  (∀x. preserves R (f x)) ∧ (∀y. preserves R (g y)) ⇒
  preserves R (case sm of INL x => f x | INR y => g y)
Proof
  Cases_on `sm` >> rw[]
QED

Theorem preserves_case_pair:
  (∀x y. preserves R (f x y)) ⇒
  preserves R (case p of (x, y) => f x y)
Proof
  Cases_on `p` >> rw[]
QED

Theorem preserves_let:
  (∀x. preserves R (f x)) ⇒
  preserves R (let x = v in f x)
Proof
  rw[]
QED

Theorem preserves_uncurry:
  (∀x y. preserves R (f x y)) ⇒
  preserves R (UNCURRY f pr)
Proof
  Cases_on `pr` >> rw[]
QED

(* ================================================================== *)
(* Composition lemmas for preserves_when                               *)
(* ================================================================== *)

Theorem preserves_when_return:
  (∀s. pre s ⇒ R s s) ⇒ preserves_when pre R (return x)
Proof
  rw[preserves_when_def, return_def]
QED

Theorem preserves_when_fail:
  (∀s. pre s ⇒ R s s) ⇒ preserves_when pre R (fail e)
Proof
  rw[preserves_when_def, fail_def]
QED

Theorem preserves_when_reraise:
  (∀s. pre s ⇒ R s s) ⇒ preserves_when pre R (reraise e)
Proof
  rw[preserves_when_def, reraise_def]
QED

Theorem preserves_when_assert:
  (∀s. pre s ⇒ R s s) ⇒ preserves_when pre R (assert b e)
Proof
  rw[preserves_when_def, assert_def, return_def, fail_def]
QED

(* Simple bind: the precondition pre is preserved by R-related
   transitions. This covers the common case where pre is a state
   invariant closed under R. *)
Theorem preserves_when_bind:
  preserves_when pre R g ∧ (∀x. preserves_when pre R (f x)) ∧
  (∀s s'. pre s ∧ R s s' ⇒ pre s') ∧
  (∀s1 s2 s3. R s1 s2 ∧ R s2 s3 ⇒ R s1 s3)
  ⇒ preserves_when pre R (bind g f)
Proof
  rw[preserves_when_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> last_x_assum drule >> rw[]
  >> last_x_assum drule >> rw[]
  >> metis_tac[]
QED

(* General bind: the continuation f x runs under a potentially
   different precondition p_cont x, which is established by the
   precondition-transfer condition. This covers the getter-bind
   pattern (e.g., after get_callee, x = head's callee). *)
Theorem preserves_when_bind_gen:
  preserves_when pre R g ∧
  (∀x. preserves_when (p_cont x) R (f x)) ∧
  (∀x s s'. g s = (INL x, s') ∧ pre s ⇒ p_cont x s') ∧
  (∀s1 s2 s3. R s1 s2 ∧ R s2 s3 ⇒ R s1 s3)
  ⇒ preserves_when pre R (bind g f)
Proof
  rw[preserves_when_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> last_x_assum drule >> rw[]
  >> last_x_assum drule >> rw[]
  >> metis_tac[]
QED

Theorem preserves_when_ignore_bind:
  preserves_when pre R g ∧ preserves_when pre R f ∧
  (∀s s'. pre s ∧ R s s' ⇒ pre s') ∧
  (∀s1 s2 s3. R s1 s2 ∧ R s2 s3 ⇒ R s1 s3)
  ⇒ preserves_when pre R (ignore_bind g f)
Proof
  rw[ignore_bind_def] >> irule preserves_when_bind >> rw[] >> metis_tac[]
QED

Theorem preserves_when_ignore_bind_gen:
  preserves_when pre R g ∧ preserves_when (p_cont u) R f ∧
  (∀s s'. g s = (INL u, s') ∧ pre s ⇒ p_cont (u:unit) s') ∧
  (∀s1 s2 s3. R s1 s2 ∧ R s2 s3 ⇒ R s1 s3)
  ⇒ preserves_when pre R (ignore_bind g f)
Proof
  rw[ignore_bind_def] >>
  irule preserves_when_bind_gen >> rw[] >> metis_tac[]
QED

Theorem preserves_when_handle:
  preserves_when pre R f ∧ (∀e. preserves_when pre R (h e)) ∧
  (∀s s'. pre s ∧ R s s' ⇒ pre s') ∧
  (∀s1 s2 s3. R s1 s2 ∧ R s2 s3 ⇒ R s1 s3)
  ⇒ preserves_when pre R (handle f h)
Proof
  rw[preserves_when_def, handle_def]
  >> gvs[AllCaseEqs()]
  >> last_x_assum drule >> rw[]
  >> last_x_assum drule >> rw[]
  >> metis_tac[]
QED

Theorem preserves_when_handle_gen:
  preserves_when pre R f ∧
  (∀e. preserves_when (h_pre e) R (h e)) ∧
  (∀e s s'. f s = (INR e, s') ∧ pre s ⇒ h_pre e s') ∧
  (∀s1 s2 s3. R s1 s2 ∧ R s2 s3 ⇒ R s1 s3)
  ⇒ preserves_when pre R (handle f h)
Proof
  rw[preserves_when_def, handle_def]
  >> gvs[AllCaseEqs()]
  >> last_x_assum drule >> rw[]
  >> last_x_assum drule >> rw[]
  >> metis_tac[]
QED

Theorem preserves_when_cond:
  preserves_when pre R m1 ∧ preserves_when pre R m2 ⇒
  preserves_when pre R (if b then m1 else m2)
Proof
  rw[]
QED

Theorem preserves_when_case_option:
  preserves_when pre R m_none ∧ (∀x. preserves_when pre R (m_some x)) ⇒
  preserves_when pre R (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem preserves_when_case_sum:
  (∀x. preserves_when pre R (f x)) ∧ (∀y. preserves_when pre R (g y)) ⇒
  preserves_when pre R (case sm of INL x => f x | INR y => g y)
Proof
  Cases_on `sm` >> rw[]
QED

Theorem preserves_when_case_pair:
  (∀x y. preserves_when pre R (f x y)) ⇒
  preserves_when pre R (case p of (x, y) => f x y)
Proof
  Cases_on `p` >> rw[]
QED

Theorem preserves_when_let:
  (∀x. preserves_when pre R (f x)) ⇒
  preserves_when pre R (let x = v in f x)
Proof
  rw[]
QED

Theorem preserves_when_uncurry:
  (∀x y. preserves_when pre R (f x y)) ⇒
  preserves_when pre R (UNCURRY f pr)
Proof
  Cases_on `pr` >> rw[]
QED

(* Conjunction for preserves_when *)
Theorem preserves_when_conj:
  preserves_when pre R1 m ∧ preserves_when pre R2 m ⇒
  preserves_when pre (λs s'. R1 s s' ∧ R2 s s') m
Proof
  rw[preserves_when_def] >> metis_tac[]
QED

Theorem preserves_when_conj_elim1:
  preserves_when pre (λs s'. R1 s s' ∧ R2 s s') m ⇒
  preserves_when pre R1 m
Proof
  rw[preserves_when_def] >> metis_tac[]
QED

Theorem preserves_when_conj_elim2:
  preserves_when pre (λs s'. R1 s s' ∧ R2 s s') m ⇒
  preserves_when pre R2 m
Proof
  rw[preserves_when_def] >> metis_tac[]
QED
