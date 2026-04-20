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
Theory vfmRunCall
Ancestors
  combin pair option pred_set list rich_list sum
  arithmetic finite_map While vfmTypes vfmConstants
  vfmContext vfmState vfmExecution vfmExecutionProp
  vfmSameFrame vfmStepLength vfmHandleStep vfmRunWithinFrame
Libs
  dep_rewrite BasicProvers

(* -------------------------------------------------------------------------
 * Active rollbacks — the list of rollbacks we could "revert to" from a
 * descendant state s of es. The current s.rollback plus the saved
 * rollbacks of every context pushed from es-depth onward (inclusive
 * of the context at es-depth itself, so that a failure-pop at
 * exactly es-depth restores a tracked rollback).
 * ------------------------------------------------------------------------- *)

Definition active_rollbacks_def:
  active_rollbacks es_depth s =
    s.rollback ::
    MAP SND (TAKE (LENGTH s.contexts - es_depth + 1) s.contexts)
End

(* -------------------------------------------------------------------------
 * Per-context outputTo-consistency. Tracks the invariant that every
 * context's `outputTo = Code a` matches `callee = a`. `vfmSameFrame`'s
 * `outputTo_consistent s` only asserts this for the head; we need the
 * per-context version to survive pops (which expose position-1 as the
 * new head).
 * ------------------------------------------------------------------------- *)

Definition outputTo_consistent_ctx_def:
  outputTo_consistent_ctx c ⇔
    ∀a. c.msgParams.outputTo = Code a ⇒ c.msgParams.callee = a
End

Definition outputTo_consistent_stack_def:
  outputTo_consistent_stack s ⇔
    s.contexts ≠ [] ∧
    EVERY outputTo_consistent_ctx (MAP FST s.contexts)
End

Theorem outputTo_consistent_stack_imp_consistent:
  outputTo_consistent_stack s ⇒ outputTo_consistent s
Proof
  rw[outputTo_consistent_stack_def, outputTo_consistent_def]
  >> Cases_on `s.contexts` >> gvs[outputTo_consistent_ctx_def]
QED

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
    outputTo_consistent_stack s ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (active_rollbacks (LENGTH es.contexts) s)
End

(* -------------------------------------------------------------------------
 * Reflexivity.
 * ------------------------------------------------------------------------- *)

Theorem run_call_inv_refl:
  outputTo_consistent_stack es ∧
  storage_slot_preserved (SND (HD es.contexts)) es.rollback ⇒
  run_call_inv es es
Proof
  rw[run_call_inv_def, active_rollbacks_def, storage_slot_preserved_def]
  >> gvs[outputTo_consistent_stack_def]
  >> Cases_on `es.contexts` >> gvs[]
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
 * `step` preserves storage at any slot not access-listed in the final
 * state. This is the core content lemma for Case 0 (same-frame step)
 * of run_call_inv_step.
 *
 * Most opcodes: `cp_step_inst_non_call[simp]` gives full accounts
 * equality (storage preserved regardless of access-listing).
 *
 * Exceptions (non-trivial cases):
 *   - SStore non-transient: `step_sstore_gas_consumption` calls
 *     `access_slot (SK address key)` BEFORE `write_storage address
 *     key value`, so any modification at `(a, k)` has `(SK a k) ∈
 *     s'.storageKeys`.
 *   - SStore transient: `write_transient_storage` modifies
 *     `tStorage`, not accounts. Storage preserved.
 *   - Log n, SelfDestruct: no storage change (logs / balance only).
 *   - Call family / Create family without grow: abort_* paths which
 *     don't change accounts, or proceed_* with grow (covered below).
 *   - Any op with inner-grow-then-pop: handle_step's set_rollback
 *     restores the pushed_rb whose accounts = s.rollback.accounts
 *     (transfer_value only changes balance).
 * ------------------------------------------------------------------------- *)

Theorem step_preserves_non_accessed_storage:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  cheat
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
  rpt strip_tac
  >> qmatch_asmsub_rename_tac `step s0 = (rr, s1)`
  >> `outputTo_consistent_stack s0` by fs[run_call_inv_def]
  >> `outputTo_consistent s0` by
       metis_tac[outputTo_consistent_stack_imp_consistent]
  >> `s0.contexts ≠ []` by fs[outputTo_consistent_def]
  >> `s1.txParams = s0.txParams`
       by metis_tac[vfmTxParamsTheory.step_preserves_txParams, SND]
  >> `s1.txParams = es.txParams` by fs[run_call_inv_def]
  >> simp[run_call_inv_def]
  (* Trichotomy on the length change. *)
  >> Cases_on `LENGTH s1.contexts = LENGTH s0.contexts` >> gvs[]
  >- (
    (* CASE 0: same-frame. *)
    `same_frame_rel s0 s1` by metis_tac[step_same_frame]
    >> `LENGTH s1.contexts = LENGTH s0.contexts ∧
        TL s1.contexts = TL s0.contexts ∧
        SND (HD s1.contexts) = SND (HD s0.contexts) ∧
        (FST (HD s1.contexts)).msgParams = (FST (HD s0.contexts)).msgParams ∧
        toSet s0.rollback.accesses.storageKeys ⊆
          toSet s1.rollback.accesses.storageKeys`
      by fs[same_frame_rel_def]
    >> `s1.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
    (* outputTo_consistent_stack s1. *)
    >> `outputTo_consistent_stack s1` by (
         fs[outputTo_consistent_stack_def]
         >> Cases_on `s0.contexts` >> Cases_on `s1.contexts` >> gvs[]
         >> gvs[outputTo_consistent_ctx_def])
    >> simp[]
    (* active_rollbacks: tail unchanged. *)
    >> `active_rollbacks (LENGTH es.contexts) s1 =
          s1.rollback :: TL (active_rollbacks (LENGTH es.contexts) s0)`
        by (simp[active_rollbacks_def]
            >> `s0.contexts ≠ [] ∧ s1.contexts ≠ []` by simp[]
            >> Cases_on `s0.contexts` >> Cases_on `s1.contexts` >> gvs[])
    >> simp[]
    (* Tail invariant transfers. *)
    >> `EVERY (λrb. storage_slot_preserved rb es.rollback)
              (TL (active_rollbacks (LENGTH es.contexts) s0))`
        by (`EVERY (λrb. storage_slot_preserved rb es.rollback)
                   (active_rollbacks (LENGTH es.contexts) s0)`
              by fs[run_call_inv_def]
            >> Cases_on `active_rollbacks (LENGTH es.contexts) s0` >> gvs[])
    >> simp[]
    (* Head: storage_slot_preserved s1.rollback es.rollback. *)
    >> `storage_slot_preserved s0.rollback es.rollback`
        by (fs[run_call_inv_def, active_rollbacks_def])
    >> simp[storage_slot_preserved_def]
    >> rpt strip_tac
    >> `¬fIN (SK a k) s0.rollback.accesses.storageKeys`
        by (fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
            >> metis_tac[])
    >> `lookup_storage k (lookup_account a s0.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage`
        by fs[storage_slot_preserved_def]
    >> drule_all step_preserves_non_accessed_storage
    >> simp[]
    >> metis_tac[])
  >> Cases_on `LENGTH s1.contexts > LENGTH s0.contexts` >> gvs[]
  >- (
    (* CASE +1: push. *)
    cheat)
  >> (
    (* CASE −1: pop. *)
    `LENGTH s1.contexts < LENGTH s0.contexts` by decide_tac
    >> cheat)
QED

(* -------------------------------------------------------------------------
 * Main run_call preservation theorem.
 * ------------------------------------------------------------------------- *)

Theorem run_call_preserves_inv:
  ∀es res es'.
    outputTo_consistent_stack es ∧
    storage_slot_preserved (SND (HD es.contexts)) es.rollback ∧
    run_call es = SOME (res, es') ⇒
    run_call_inv es es'
Proof
  rpt strip_tac
  >> `es.contexts ≠ []` by fs[outputTo_consistent_stack_def]
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
       >> Cases_on `es.contexts` >> gvs[outputTo_consistent_stack_def])
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
    outputTo_consistent_stack es ∧
    storage_slot_preserved (SND (HD es.contexts)) es.rollback ∧
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
    outputTo_consistent_stack es ∧
    storage_slot_preserved (SND (HD es.contexts)) es.rollback ∧
    run_call es = SOME (r, es') ⇒
    es'.txParams = es.txParams
Proof
  rpt strip_tac
  >> drule_all run_call_preserves_inv
  >> rw[run_call_inv_def]
QED
