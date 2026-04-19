(* ==========================================================================
 * vfmRunCallScript.sml
 *
 * Preservation theorems across a whole call (run_call). The headline theorem
 * is run_call_preserves_storage_outside_accessed: storage of any address not
 * in the final accessed set is unchanged.
 *
 * Strategy: OWHILE_INV_IND over run_call with a 2-state invariant that
 * tracks:
 *   1. A "same-frame" conjunction between es and s (msdomain compatibility,
 *      txParams equality, gasUsed/refund/logs monotonicity on the initial
 *      head if still present, access growth at the bottom of the stack).
 *   2. A storage invariant for every "active rollback" — the chain of
 *      rollbacks we could revert to, namely s.rollback plus the saved
 *      rollbacks of every context pushed on top of es.
 *
 * The second clause is what makes the induction go through: a revert
 * transition replaces s.rollback with the saved rollback of the popped
 * head, but that was already known to satisfy the storage invariant, so
 * the invariant is preserved across reverts.
 * ========================================================================== *)

open HolKernel boolLib bossLib Parse dep_rewrite BasicProvers
     combinTheory pairTheory optionTheory pred_setTheory listTheory
     rich_listTheory sumTheory arithmeticTheory finite_mapTheory
     WhileTheory
     vfmTypesTheory vfmConstantsTheory vfmContextTheory vfmStateTheory
     vfmExecutionTheory vfmExecutionPropTheory
     vfmCallFrameTheory;

val _ = new_theory "vfmRunCall";

(* -------------------------------------------------------------------------
 * Active rollbacks — the set of rollbacks we could "revert to" from a
 * descendant state s of es. The current s.rollback plus the saved
 * rollbacks of every context pushed after es's depth.
 * ------------------------------------------------------------------------- *)

Definition active_rollbacks_def:
  active_rollbacks es_depth s =
    s.rollback :: MAP SND (TAKE (LENGTH s.contexts - es_depth) s.contexts)
End

(* -------------------------------------------------------------------------
 * The 2-state run_call invariant.
 * ------------------------------------------------------------------------- *)

Definition storage_preserved_def:
  storage_preserved rb rb0 ⇔
    ∀a. ¬fIN a rb.accesses.addresses ⇒
        (lookup_account a rb.accounts).storage =
        (lookup_account a rb0.accounts).storage
End

Definition tStorage_preserved_def:
  tStorage_preserved rb rb0 ⇔
    ∀a. ¬fIN a rb.accesses.addresses ⇒
        rb.tStorage a = rb0.tStorage a
End

Definition code_preserved_def:
  code_preserved rb rb0 ⇔
    ∀a. ¬fIN a rb.accesses.addresses ⇒
        (lookup_account a rb.accounts).code =
        (lookup_account a rb0.accounts).code
End

Definition run_call_inv_def:
  run_call_inv es s ⇔
    s.txParams = es.txParams ∧
    EVERY (λrb. storage_preserved rb es.rollback)
          (active_rollbacks (LENGTH es.contexts) s)
End

(* -------------------------------------------------------------------------
 * Single-step preservation of run_call_inv. TODO — depends on
 * step_same_frame + characterisation of rollback mutations per step.
 * ------------------------------------------------------------------------- *)

Theorem run_call_inv_refl:
  es.contexts ≠ [] ⇒ run_call_inv es es
Proof
  rw[run_call_inv_def, active_rollbacks_def, storage_preserved_def]
QED

Theorem run_call_inv_step:
  ∀es s s' r.
    es.contexts ≠ [] ∧
    run_call_inv es s ∧
    LENGTH s.contexts ≥ LENGTH es.contexts ∧
    step s = (r, s') ⇒
    run_call_inv es s'
Proof
  cheat
QED

(* -------------------------------------------------------------------------
 * Main run_call preservation theorem.
 * ------------------------------------------------------------------------- *)

Theorem run_call_preserves_inv:
  ∀es res es'.
    es.contexts ≠ [] ∧
    run_call es = SOME (res, es') ⇒
    run_call_inv es es'
Proof
  rpt strip_tac
  >> gvs[run_call_def]
  >> `(λ p. run_call_inv es (SND p)) (res, es')` suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[run_call_inv_refl]
  >> rpt gen_tac
  >> pairarg_tac >> simp[]
  >> strip_tac
  >> Cases_on `step s''` >> simp[]
  >> `s''.contexts ≠ []` by (
       Cases_on `s''.contexts` >> gvs[]
       >> Cases_on `es.contexts` >> gvs[])
  >> irule run_call_inv_step
  >> simp[]
  >> qexistsl_tac [`q`, `s''`]
  >> simp[]
QED

(* -------------------------------------------------------------------------
 * Named headline corollaries.
 * ------------------------------------------------------------------------- *)

Theorem run_call_preserves_storage_outside_accessed:
  ∀es r es'.
    es.contexts ≠ [] ∧
    run_call es = SOME (r, es') ⇒
    ∀a. ¬fIN a es'.rollback.accesses.addresses ⇒
        (lookup_account a es'.rollback.accounts).storage =
        (lookup_account a es.rollback.accounts).storage
Proof
  rpt strip_tac
  >> drule_all run_call_preserves_inv
  >> rw[run_call_inv_def, active_rollbacks_def, storage_preserved_def]
QED

Theorem run_call_preserves_txParams:
  ∀es r es'.
    es.contexts ≠ [] ∧
    run_call es = SOME (r, es') ⇒
    es'.txParams = es.txParams
Proof
  rpt strip_tac
  >> drule_all run_call_preserves_inv
  >> rw[run_call_inv_def]
QED

val _ = export_theory ();
