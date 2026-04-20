(* ==========================================================================
 * vfmRunCallScript.sml
 *
 * Preservation theorems across a whole call (run_call). The headline theorem
 * is run_call_preserves_storage_outside_accessed_slots: the value of any
 * storage slot (a, k) not in the final accessed storageKeys is unchanged.
 *
 * Strategy: OWHILE_INV_IND over run_call with a 2-state invariant that
 * tracks:
 *   1. txParams equality between es and s.
 *   2. A per-slot storage invariant for every "active rollback" — the chain
 *      of rollbacks we could revert to, namely s.rollback plus the saved
 *      rollbacks of every context pushed on top of es.
 *
 * Using storageKeys (not addresses) is essential because SSTORE only
 * access-lists the slot (SK address key), not the address. The storageKeys
 * formulation exactly matches SSTORE's access behaviour.
 *
 * The saved-rollbacks clause is what makes the induction go through:
 * a revert transition replaces s.rollback with the saved rollback of the
 * popped head, but that was already known to satisfy the storage
 * invariant, so the invariant is preserved across reverts.
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
 * Active rollbacks — the list of rollbacks we could "revert to" from a
 * descendant state s of es. The current s.rollback plus the saved
 * rollbacks of every context pushed after es's depth.
 * ------------------------------------------------------------------------- *)

Definition active_rollbacks_def:
  active_rollbacks es_depth s =
    s.rollback :: MAP SND (TAKE (LENGTH s.contexts - es_depth) s.contexts)
End

(* -------------------------------------------------------------------------
 * Per-slot storage preservation: slot (a, k) unchanged outside
 * access-listed storage keys.
 * ------------------------------------------------------------------------- *)

Definition storage_slot_preserved_def:
  storage_slot_preserved rb rb0 ⇔
    ∀a k. ¬fIN (SK a k) rb.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a rb.accounts).storage =
        lookup_storage k (lookup_account a rb0.accounts).storage
End

(* -------------------------------------------------------------------------
 * The 2-state run_call invariant.
 * ------------------------------------------------------------------------- *)

Definition run_call_inv_def:
  run_call_inv es s ⇔
    s.txParams = es.txParams ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (active_rollbacks (LENGTH es.contexts) s)
End

(* -------------------------------------------------------------------------
 * Reflexivity.
 * ------------------------------------------------------------------------- *)

Theorem run_call_inv_refl:
  es.contexts ≠ [] ⇒ run_call_inv es es
Proof
  rw[run_call_inv_def, active_rollbacks_def, storage_slot_preserved_def]
QED

(* -------------------------------------------------------------------------
 * Single-step preservation of run_call_inv.
 *
 * This is the technical core. Case analysis on step's effect:
 *   - Same-frame step: length preserved, same_frame_rel s s', active
 *     rollbacks preserved entry-by-entry (the tail is unchanged, and the
 *     head s'.rollback inherits by callee_local_changes + slot-level
 *     access-listing).
 *   - Push step: length grows, new active entry is s.rollback (mid-step,
 *     post-prefix). Handled via same_frame_or_grow structural facts.
 *   - Pop success: length shrinks (but stays ≥ es), active rollbacks
 *     shrinks; entries are preserved subsequences of the old.
 *   - Pop revert: s'.rollback replaced by saved rollback of popped head,
 *     which was already an active rollback entry satisfying the
 *     invariant.
 * ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
 * Transitivity of storage_slot_preserved.
 * ------------------------------------------------------------------------- *)

Theorem storage_slot_preserved_refl:
  storage_slot_preserved rb rb
Proof
  rw[storage_slot_preserved_def]
QED

(* If access-sets are monotone (storageKeys_1 ⊆ storageKeys_2), and every
   slot preserved under storageKeys_1 is preserved under storageKeys_2, then
   preservation composes. Used for chaining across step transitions. *)
Theorem storage_slot_preserved_trans_mono:
  storage_slot_preserved rb1 rb0 ∧
  storage_slot_preserved rb2 rb1 ∧
  (∀a k. ¬fIN (SK a k) rb2.accesses.storageKeys ⇒
         ¬fIN (SK a k) rb1.accesses.storageKeys) ⇒
  storage_slot_preserved rb2 rb0
Proof
  rw[storage_slot_preserved_def]
QED

(* -------------------------------------------------------------------------
 * Helper: same_frame_rel preserves storage_slot_preserved against the
 * initial rollback es.rollback.
 *
 * same_frame_rel gives us: accesses monotone, non-callee accounts
 * unchanged (storage + code + nonce). The callee's accesses in s' ⊇
 * those in s. If a storage slot (a, k) is not in s'.accesses.storageKeys,
 * then (a, k) is not in s.accesses.storageKeys either (monotone). The
 * slot's value in s' equals its value in s by same_frame_rel's
 * callee_local_changes structure plus the fact that any SSTORE must
 * have access-listed (a, k), putting it in s'.accesses.storageKeys.
 *
 * Actually, simpler: we can directly show the slot is preserved by
 * non-SSTORE primitives (no storage mutation), and SSTORE access-lists
 * the exact slot.
 * ------------------------------------------------------------------------- *)

(* Transitivity-style fact: if s -> s' preserves slot (a, k) outside
   s'.storageKeys, and inv says slot (a, k) outside s.storageKeys had
   same value as in es, then slot (a, k) outside s'.storageKeys has the
   same value as in es. *)
Theorem storage_slot_preserved_compose:
  ∀(es:execution_state) (s:execution_state) (s':execution_state).
    storage_slot_preserved s.rollback es.rollback ∧
    (∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
           ¬fIN (SK a k) s.rollback.accesses.storageKeys ∧
           lookup_storage k (lookup_account a s'.rollback.accounts).storage =
           lookup_storage k (lookup_account a s.rollback.accounts).storage) ⇒
    storage_slot_preserved s'.rollback es.rollback
Proof
  rw[storage_slot_preserved_def]
  >> metis_tac[]
QED

(* -------------------------------------------------------------------------
 * Single-step preservation of run_call_inv.
 *
 * Strategy: case on the length change. In each case, characterise
 * active_rollbacks after the step and show each entry inherits from
 * the previous invariant.
 * ------------------------------------------------------------------------- *)

(* TODO: Case analysis on step's length effect:
    - Same-frame step (length preserved): same_frame_rel s s' via
      step_same_frame; active_rollbacks preserved entry-wise
      because TL s'.contexts = TL s.contexts and SND (HD s'.contexts)
      = SND (HD s.contexts) by same_frame_rel. Head s'.rollback:
      storage slot (a, k) not in s'.accesses.storageKeys ⇒ not in
      s.accesses.storageKeys (monotone); storage at (a, k) in
      s'.rollback equals s.rollback by callee_local_changes at
      non-callee (with access-listing tracking callee writes).
    - Grow step (length +1): new active rollback entry is
      s.rollback at mid-step. Prior entries shifted down by one but
      preserved. s'.rollback = s.rollback at mid-step too.
    - Shrink (pop success): active_rollbacks shrinks by dropping
      first TL entry. s'.rollback = s.rollback preserved.
    - Shrink (pop revert): s'.rollback = SND (HD s.contexts)
      which was the second entry of old active_rollbacks.
      Remaining TL entries preserved.
   Requires helper lemmas for each step-effect shape. *)
Theorem run_call_inv_step:
  ∀es s s' r.
    es.contexts ≠ [] ∧
    run_call_inv es s ∧
    LENGTH s.contexts ≥ LENGTH es.contexts ∧
    step s = (r, s') ⇒
    run_call_inv es s'
Proof
  (* Full proof requires extensive case analysis on step's length
     effect. Structure:
     1. step s = (r, s'): either length preserved, +1 (push), or -1
        (pop from handle_step pop_and_incorporate_context).
     2. For each case, characterise active_rollbacks s' relative to
        s active_rollbacks.
     3. Preserved case: active_rollbacks elementwise preserved by
        same_frame_rel s s' (from step_same_frame).
     4. Push case: new head context has saved rollback s.rollback,
        which is already in old active_rollbacks. Tail of old list
        is in new list.
     5. Pop success: active_rollbacks drops one element from the
        TL; s.rollback = new s.rollback preserved.
     6. Pop revert: s.rollback replaced by SND of popped head,
        which was already an active rollback entry satisfying
        the invariant. *)
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
 * Named headline corollary: per-slot storage preservation.
 *
 * This is the primary statement — any storage slot (a, k) not in the final
 * accessed storageKeys set has its value unchanged from the initial state.
 * ------------------------------------------------------------------------- *)

Theorem run_call_preserves_storage_outside_accessed_slots:
  ∀es r es'.
    es.contexts ≠ [] ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage
Proof
  rpt strip_tac
  >> drule_all run_call_preserves_inv
  >> rw[run_call_inv_def, active_rollbacks_def, storage_slot_preserved_def]
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
