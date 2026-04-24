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
  vfmStoragePredicates vfmSameFrame vfmStaticCalls vfmStepLength vfmHandleStep vfmRunWithinFrame
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
    (if LENGTH s.contexts < es_depth then []
     else MAP SND (TAKE (LENGTH s.contexts - es_depth + 2) s.contexts))
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
  EVERY (λrb. storage_slot_preserved rb es.rollback)
        (MAP SND (TAKE 2 es.contexts)) ⇒
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

(* The theorem, specialised to the same-frame case (Case 0 of
   run_call_inv_step). Works because:
   - same_frame_rel gives callee_local_changes: storage at every
     non-callee address is preserved unconditionally.
   - At the callee address: the only step_inst that modifies callee
     storage is step_sstore F (non-transient SSTORE), and
     step_sstore_gas_consumption calls access_slot (SK callee key)
     BEFORE write_storage. So any modification at (callee, k) adds
     (SK callee k) to s'.rollback.accesses.storageKeys; contrapositive
     gives preservation at unaccessed callee slots.
   - Cases +1 and −1 of run_call_inv_step don't rely on this lemma
     (they have their own structural arguments via step_push_structure
     and step_pop_structure). *)
(* Key auxiliary: if write_storage address key value runs starting
   from state t, then the final state has (SK address key) in its
   storageKeys. This is by definition — write_storage uses
   update_accounts which only touches accounts, and storageKeys is in
   rollback.accesses, which is not touched. So if storageKeys already
   contained SK address key, it still does; if not, it still doesn't.
   Actually: write_storage does NOT add to accesses.storageKeys. The
   access-listing happens separately via access_slot in
   step_sstore_gas_consumption. *)

(* Direct proof: factor out the observation that for same-frame step,
   if (SK callee key) is NOT in s'.storageKeys, then the SSTORE path
   was not taken for that slot. *)

(* The actual callee storage analysis: in step, the only primitive that
   writes callee storage is write_storage callee key _ . This is only
   called inside step_sstore F callee (via step_sstore_def). Before it,
   step_sstore_gas_consumption calls access_slot (SK callee key),
   which adds (SK callee key) to storageKeys. Afterwards (and in the
   rest of the step), accesses only grow. So any storage change at
   (callee, key) implies (SK callee key) ∈ s'.storageKeys. *)


(* =====================================================================
 * proceed_call / proceed_create strictly grow contexts.
 *
 * Both contain an unconditional push_context, and all following ops
 * are preserves_same_frame (length-preserving).
 * ===================================================================== *)

Theorem proceed_call_grows_contexts:
  proceed_call op sender address value argsOffset argsSize code stipend
                outputTo s = (r, s') ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts > LENGTH s.contexts
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def]
  >> simp[bind_def, get_rollback_def, return_def]
  >> simp[read_memory_def, bind_def,return_def, get_current_context_def]
  >> qmatch_goalsub_abbrev_tac`ignore_bind g`
  >> simp[ignore_bind_def, Once bind_def]
  >> TOP_CASE_TAC
  >> qmatch_asmsub_rename_tac`g s = (q,s1)`
  >> `LENGTH s1.contexts = LENGTH s.contexts ∧ ISL q` by (
    gvs[Abbr`g`,AllCaseEqs(),COND_RATOR,return_def,update_accounts_def] )
  >> TOP_CASE_TAC >> gvs[]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
  >> IF_CASES_TAC >> gvs[]
  >> rewrite_tac[Once bind_def]
  >> simp[get_value_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_value_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_static_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_static_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> TOP_CASE_TAC
  >> drule push_context_effect >> strip_tac >> gvs[]
  >> reverse IF_CASES_TAC
  >> simp[return_def]
  >- ( strip_tac >> gvs[] )
  >> strip_tac >>
  qmatch_assum_abbrev_tac`dispatch_precompiles a ss = _` >>
  assume_tac (INST_TYPE[alpha |-> ``:unit``]preserves_same_frame_dispatch_precompiles) >>
  drule_then drule (INST_TYPE[alpha |-> ``:unit``]psf_imp_length_contexts_preserved) >>
  simp[Abbr`ss`]
QED

Theorem proceed_create_grows_contexts:
  proceed_create senderAddress address value code cappedGas s = (r, s')
  ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts > LENGTH s.contexts
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def]
  (* update_accounts (increment_nonce senderAddress) *)
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  (* get_rollback *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  (* get_original *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  (* set_original: s' = s with contexts := set_last_accounts _ s.contexts *)
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  (* update_accounts (transfer_value o increment_nonce) *)
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  (* push_context *)
  >> strip_tac
  >> drule push_context_effect >> strip_tac >> gvs[]
  (* Length goal: set_last_accounts preserves length. *)
  >> simp[set_last_accounts_def, listTheory.LENGTH_SNOC,
          rich_listTheory.LENGTH_FRONT]
QED

(* =====================================================================
 * Pushed-rollback storage lemmas.
 *
 * When step_call / step_create grows contexts by +1, the saved
 * rollback at the new head (SND (HD s'.contexts)) has the same
 * .accounts.storage as s.rollback.accounts.storage.
 *
 * Proof sketch:
 *   - step_call/step_create run preserves_storage primitives until
 *     they reach proceed_call/proceed_create.
 *   - proceed_call/proceed_create:
 *       rollback <- get_rollback;       (* captures rb with same storage *)
 *       ... preserves_storage prefix ...
 *       push_context (context, rollback);
 *       (optional) dispatch_precompiles (preserves_rollback; doesn't touch SND HD)
 *   - After push_context, SND (HD s'.contexts) = rollback captured above,
 *     whose .accounts.storage equals s.rollback.accounts.storage.
 *   - The subsequent ops (set_current_context inside precompiles,
 *     consume_gas, set_return_data, finish) only touch FST (HD contexts)
 *     or s.rollback, never SND (HD contexts).
 * ===================================================================== *)

(* Intermediate: proceed_call captures s.rollback as the pushed rollback.
   Since get_rollback is the first thing that matters and nothing before
   it touches storage, the captured rollback's .accounts.storage equals
   s.rollback.accounts.storage. dispatch_precompiles afterwards is
   preserves_same_frame, so SND (HD ·) is unchanged. *)
Theorem proceed_call_pushed_rb_storage:
  proceed_call op sender address value argsOffset argsSize code stipend
                outputTo s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
      (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def]
  (* get_rollback captures s.rollback. *)
  >> simp[bind_def, get_rollback_def, return_def]
  >> simp[read_memory_def, bind_def, return_def, get_current_context_def]
  >> qmatch_goalsub_abbrev_tac `ignore_bind g`
  >> simp[ignore_bind_def, Once bind_def]
  >> TOP_CASE_TAC
  >> qmatch_asmsub_rename_tac `g s = (q, s1)`
  (* g is either update_accounts (transfer_value ...) or return () — both
     preserve storage of s.rollback.accounts at every address. *)
  >> `∀a. (lookup_account a s1.rollback.accounts).storage =
         (lookup_account a s.rollback.accounts).storage`
      by (`preserves_storage g`
            by (simp[Abbr`g`] >> IF_CASES_TAC >> simp[])
          >> fs[preserves_storage_def] >> first_x_assum drule >>
          rw[lookup_storage_def] >> gvs[FUN_EQ_THM])
  >> `ISL q` by (gvs[Abbr`g`,AllCaseEqs(),COND_RATOR,return_def,
                     update_accounts_def])
  >> TOP_CASE_TAC >> gvs[]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
  >> IF_CASES_TAC >> gvs[fail_def] >- (rw[] >> gvs[])
  >> rewrite_tac[Once bind_def]
  >> simp[get_value_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_value_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_static_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_static_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> TOP_CASE_TAC
  >> drule push_context_effect >> strip_tac >> gvs[]
  (* After push_context: HD = (context, s1.rollback-like). Specifically,
     push_context (c, rollback) where `rollback` was captured by get_rollback
     after g ran. So HD s_after_push.contexts = (c, s1.rollback). *)
  >> qmatch_asmsub_abbrev_tac `push_context (ctx, _) s1`
  >> reverse IF_CASES_TAC >> simp[return_def]
  >- ((* No precompile: result state has HD = (ctx, s1.rollback). *)
      strip_tac >> gvs[])
  (* Precompile: dispatch_precompiles runs after push. It is
     preserves_same_frame at the new depth, so SND (HD ·) is invariant. *)
  >> strip_tac
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles addr ss = (_, s')`
  >> `ss.contexts ≠ []` by simp[Abbr`ss`]
  >> qmatch_asmsub_abbrev_tac`dpa ss = (_,_)`
  >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
  >> pop_assum mp_tac
  >> rewrite_tac[preserves_same_frame_def]
  >> disch_then drule
  >> `ss.contexts = (ctx, s.rollback) :: s1.contexts` by simp[Abbr`ss`]
  >> simp[same_frame_rel_def]
QED

(* Intermediate: proceed_create captures s.rollback (post increment_nonce)
   as the pushed rollback. increment_nonce and set_original do not touch
   s.rollback.accounts.storage. transfer_value happens AFTER get_rollback,
   so it doesn't affect the captured rollback. *)
Theorem proceed_create_pushed_rb_storage:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
      (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def]
  (* update_accounts (increment_nonce senderAddress) *)
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  (* get_rollback: captures increment_nonce'd rollback. *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  (* get_original / set_original: don't modify s.rollback. *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  (* update_accounts (transfer_value o increment_nonce): modifies s.rollback,
     but the captured `rollback` variable already holds the pre-transfer one. *)
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  (* push_context. *)
  >> strip_tac
  >> drule push_context_effect >> strip_tac >> gvs[]
  (* After push: HD s'.contexts = (ctx, rollback-with-incremented-nonce).
     increment_nonce preserves storage at every address. *)
  >> rw[lookup_account_def, increment_nonce_def,
        combinTheory.APPLY_UPDATE_THM, finite_mapTheory.FLOOKUP_UPDATE]
  >> gvs[update_account_def, APPLY_UPDATE_THM]
  >> rw[]
QED

(* Wrapper: step_call runs preserves_storage primitives (pop_stack, consume_gas,
   memory_expansion, access_address, ...) until it reaches either an abort
   branch (which does not grow) or proceed_call (which grows and is handled
   by proceed_call_pushed_rb_storage above). For the grow case, the state
   just before proceed_call has the same storage as s (by preserves_storage
   of all the prefix ops), so proceed_call_pushed_rb_storage gives us what
   we need. *)
(* Helper principle: if a monad m is preserves_storage and
   preserves_same_frame, and bind m f s = (r, s'), then we can
   replace s by an intermediate s_mid — with same storage and
   contexts as s — and reduce to proving the property for f at s_mid. *)

(* We use the following shape for step_call/step_create:

     step_call = do ...preserves_storage_prefix... ;
                    if cond1 then abort_call_value stipend
                    else do ...preserves_storage_prefix'... ;
                           if cond2 then abort_unuse stipend
                           else proceed_call ... od od

   The prefixes are preserves_storage + preserves_same_frame. The two
   abort branches are preserves_same_frame (hence don't grow contexts).
   Only proceed_call grows. *)

(* -----------------------------------------------------------------
 * preserves_pushed_rb_storage: a monad m preserves the pushed rollback
 * storage at every address that was valid before m ran.
 *
 * Formally: if m s = (r, s') and LENGTH s'.contexts > LENGTH s.contexts
 * then the new top frame's saved rollback has the same .accounts.storage
 * as s.rollback.accounts.storage at every address.
 *
 * This lets us compose: a bind of two ops that each "preserves pushed rb
 * storage when growing" does so. A preserves_storage + preserves_same_frame
 * prefix IS `preserves_pushed_rb_storage` vacuously (it can't grow).
 * ----------------------------------------------------------------- *)
Definition preserves_pushed_rb_storage_def:
  preserves_pushed_rb_storage (m : α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ∧
             LENGTH s'.contexts > LENGTH s.contexts ⇒
      ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
          (lookup_account a s.rollback.accounts).storage
End

(* preserves_storage + preserves_same_frame ⇒ preserves_pushed_rb_storage
   vacuously (same_frame rules out LENGTH growth). *)
Theorem preserves_pushed_rb_storage_of_same_frame[simp]:
  preserves_same_frame m ⇒ preserves_pushed_rb_storage m
Proof
  rw[preserves_same_frame_def, preserves_pushed_rb_storage_def]
  >> first_x_assum drule >> simp[same_frame_rel_def]
QED

(* bind composition: if g preserves_pushed_rb_storage AND
   (preserves_storage g ∧ preserves_same_frame g), and f x
   preserves_pushed_rb_storage for all x, then bind g f does. *)
Theorem preserves_pushed_rb_storage_bind:
  preserves_storage g ∧ preserves_same_frame g ∧
  (∀x. preserves_pushed_rb_storage (f x)) ⇒
  preserves_pushed_rb_storage (bind g f)
Proof
  rw[preserves_pushed_rb_storage_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> fs[preserves_storage_def, preserves_same_frame_def]
  >> rpt (first_x_assum drule) >> simp[same_frame_rel_def] >> strip_tac
  >> rpt strip_tac
  (* intermediate s_mid after g: same contexts, same storage. *)
  >> qmatch_asmsub_rename_tac `g s = (_, s_mid)`
  >> `s_mid.contexts ≠ []` by (Cases_on `s.contexts` >> Cases_on `s_mid.contexts` >> fs[])
  >> `LENGTH s'.contexts > LENGTH s_mid.contexts` by fs[]
  >> first_x_assum drule >> simp[]
  >> disch_then (qspec_then `a` mp_tac) >> simp[]
  >> gvs[lookup_storage_def, FUN_EQ_THM]
QED

Theorem preserves_pushed_rb_storage_ignore_bind:
  preserves_storage g ∧ preserves_same_frame g ∧
  preserves_pushed_rb_storage f ⇒
  preserves_pushed_rb_storage (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule preserves_pushed_rb_storage_bind >> rw[]
QED

Theorem preserves_pushed_rb_storage_cond[simp]:
  preserves_pushed_rb_storage m1 ∧ preserves_pushed_rb_storage m2 ⇒
  preserves_pushed_rb_storage (if b then m1 else m2)
Proof
  rw[]
QED

(* Base case: proceed_call preserves pushed rb storage. *)
Theorem preserves_pushed_rb_storage_proceed_call[simp]:
  preserves_pushed_rb_storage
    (proceed_call op sender address value argsOffset argsSize
                  code stipend outputTo)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all proceed_call_pushed_rb_storage
  >> simp[]
QED

Theorem preserves_pushed_rb_storage_proceed_create[simp]:
  preserves_pushed_rb_storage
    (proceed_create senderAddress address value code cappedGas)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all proceed_create_pushed_rb_storage
  >> simp[]
QED

(* Now step_call = a bunch of preserves_storage+preserves_same_frame
   primitives followed by either abort_call_value (which is
   preserves_same_frame, vacuously preserves_pushed_rb_storage),
   abort_unuse (likewise), or proceed_call. *)
Theorem preserves_pushed_rb_storage_step_call[simp]:
  preserves_pushed_rb_storage (step_call op)
Proof
  simp[step_call_def]
  (* Shape mirrors preserves_storage_step_call's proof. Every bind
     prefix is preserves_storage + preserves_same_frame; use the
     bind rule with those two side conditions. *)
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[]
  >> reverse conj_tac >- (CASE_TAC >> simp[])
  >> Cases >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
QED

(* abort_create_exists doesn't grow contexts, so vacuously preserves
   pushed-rb storage. Unlike abort_call_value/abort_unuse, it is NOT
   unconditionally preserves_same_frame (it requires the sender address
   to match the current callee), so we prove it from the length lemma. *)
Theorem preserves_pushed_rb_storage_abort_create_exists[simp]:
  preserves_pushed_rb_storage (abort_create_exists a)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all abort_create_exists_length
  >> simp[]
QED

Theorem preserves_pushed_rb_storage_step_create[simp]:
  preserves_pushed_rb_storage (step_create two)
Proof
  simp[step_create_def]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> rpt (irule preserves_pushed_rb_storage_ignore_bind >> simp[])
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> rpt (irule preserves_pushed_rb_storage_ignore_bind >> simp[])
  >> irule preserves_pushed_rb_storage_cond >> simp[]
  >> irule preserves_pushed_rb_storage_cond >> simp[]
QED

(* Final user-facing lemmas. *)
Theorem step_call_pushed_rb_storage:
  ∀op s r s'. step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
        (lookup_account a s.rollback.accounts).storage
Proof
  metis_tac[preserves_pushed_rb_storage_step_call,
            preserves_pushed_rb_storage_def]
QED

Theorem step_create_pushed_rb_storage:
  ∀two s r s'. step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
        (lookup_account a s.rollback.accounts).storage
Proof
  metis_tac[preserves_pushed_rb_storage_step_create,
            preserves_pushed_rb_storage_def]
QED

(* A helper: the gas/return-data prefix of handle_exception is preserves_rollback. *)
Theorem preserves_rollback_handle_exception_prefix:
  preserves_rollback
    (if b then
       ignore_bind (bind get_gas_left (λgasLeft. consume_gas gasLeft))
                   (set_return_data [])
     else return ())
Proof
  Cases_on `b` >> rw[]
  >> irule preserves_rollback_ignore_bind >> rw[]
QED

(* handle_exception with num_contexts ≤ 1 preserves rollback:
   only the reraise branch runs (after consume_gas + set_return_data
   which are preserves_rollback). *)
(* handle_exception when LENGTH is preserved: rollback is preserved.
   Because handle_exception's structure takes the n ≤ 1 branch when
   length is preserved (n > 1 would pop). In the n ≤ 1 branch only
   preserves_rollback primitives run. *)
Theorem handle_exception_same_length_preserves_rollback:
  handle_exception e s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  s'.rollback = s.rollback
Proof
  simp[handle_exception_def] >>
  qmatch_goalsub_abbrev_tac`ignore_bind prefix _` >>
  simp[ignore_bind_def, bind_def] >>
  TOP_CASE_TAC >>
  `r'.rollback = s.rollback ∧ LENGTH r'.contexts = LENGTH s.contexts` by (
    gvs[Abbr`prefix`,return_def,AllCaseEqs(),COND_RATOR,
        bind_def,ignore_bind_def,get_gas_left_def,
        get_current_context_def,fail_def,return_def,
        consume_gas_def,set_current_context_def,
        set_return_data_def,assert_def] >>
    Cases_on`s.contexts` >> gvs[] ) >>
  reverse TOP_CASE_TAC >- (rw[] >> gvs[]) >>
  simp[get_num_contexts_def, return_def] >>
  IF_CASES_TAC >- (rw[reraise_def] >> gvs[]) >>
  simp[bind_def, get_return_data_def, get_output_to_def, return_def,
       get_current_context_def] >>
  IF_CASES_TAC >> gvs[] >>
  TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac`pop_and_incorporate_context _ s1 = (r2, s2)` >>
  `s2.contexts <> [] ∧ (ISR r2 ⇒ s2.rollback = s1.rollback)
   ∧ (ISL r2 ⇒ LENGTH s2.contexts < LENGTH s1.contexts)` by (
    gvs[pop_and_incorporate_context_def] >>
    gvs[bind_def, AllCaseEqs(),ignore_bind_def,get_gas_left_def,return_def,
        pop_context_def,fail_def,get_current_context_def,unuse_gas_def,
        assert_def,set_current_context_def,COND_RATOR,
        update_gas_refund_def,push_logs_def,set_rollback_def] >>
    Cases_on`s1.contexts` >> gvs[] ) >>
  reverse TOP_CASE_TAC >- (rw[] >> gvs[]) >>
  gvs[] >>
  simp[inc_pc_def, get_current_context_def, return_def, bind_def,
       ignore_bind_def,set_current_context_def] >>
  simp[AllCaseEqs(), return_destination_CASE_rator, bind_def,
       ignore_bind_def, set_return_data_def, get_current_context_def,
       return_def, push_stack_def, assert_def, COND_RATOR, fail_def] >>
  rw[] >> gvs[set_current_context_def, return_def] >>
  qmatch_asmsub_abbrev_tac`write_memory i bs` >>
  mp_tac preserves_same_frame_write_memory >>
  rewrite_tac[preserves_same_frame_def] >>
  disch_then drule >>
  simp[same_frame_rel_def]
QED

(* handle_step preserves storage when it preserves length.
   Under same_frame_rel (from handle_step_same_frame), storage at
   non-callee is preserved by callee_local_changes. At callee,
   no SSTORE runs in handle_step (handle_create only touches .code,
   handle_exception doesn't touch .storage). *)

(* DEMO CHEAT: demonstrate how to apply `handle_create_INR` when
   we have an INL hypothesis that should be impossible.
   handle_create_INR : ⊢ s.contexts ≠ [] ⇒
     ∃e' s'. handle_create e s = (INR e', s') *)
Theorem demo_handle_create_INL_impossible:
  s.contexts ≠ [] ∧ handle_create y s = (INL v, r) ⇒ F
Proof
  strip_tac >>
  drule handle_create_INR >>
  rename1`handle_create e` >>
  disch_then(qspec_then`e`mp_tac) >> rw[]
QED

Theorem handle_step_preserves_storage_same_length:
  s.contexts ≠ [] ∧ outputTo_consistent s ∧
  handle_step y s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rw[handle_step_def, reraise_def, handle_def]
  >> gvs[AllCaseEqs()]
  >- (
    (* handle_create returned INL — impossible by handle_create_INR. *)
    drule (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
    >> rename1 `handle_create e`
    >> disch_then (qspec_then `e` mp_tac) >> rw[])
  (* handle_create returned INR eout; handle_exception eout s'' = (r, s'). *)
  >> rename1 `handle_create y s = (INR eout, s'')`
  >> mp_tac (INST_TYPE [alpha |-> ``:unit``]
              (GEN_ALL preserves_storage_handle_create))
  >> simp[preserves_storage_def]
  >> disch_then drule >> rw[]
  >> `same_frame_rel s s''` by (
       mp_tac (Q.SPEC `y`
                (Q.GEN `e`
                  (SIMP_RULE std_ss [psf_def]
                    (INST_TYPE [alpha |-> ``:unit``] psf_handle_create))))
       >> disch_then drule
       >> simp[])
  >> `s''.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
  >> `LENGTH s''.contexts = LENGTH s.contexts` by fs[same_frame_rel_def]
  >> `LENGTH s'.contexts = LENGTH s''.contexts` by simp[]
  >> `s'.rollback = s''.rollback`
       by metis_tac[handle_exception_same_length_preserves_rollback]
  >> simp[]
QED

(* =====================================================================
 * Helpers for step_push_structure / step_pop_structure.
 * ===================================================================== *)

(* handle_exception: pop_and_incorporate_context is the only place that
   reduces contexts. It reduces by one. So handle_exception shrinks by at
   most one. *)
Theorem handle_exception_shrinks_by_one:
  handle_exception e s = (q, s') ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts + 1 ≥ LENGTH s.contexts ∧
  LENGTH s'.contexts ≤ LENGTH s.contexts
Proof
  strip_tac
  >> qhdtm_x_assum `handle_exception` mp_tac
  >> simp[handle_exception_def]
  >> simp[ignore_bind_def, Once bind_def]
  >> qmatch_goalsub_abbrev_tac `prefix s`
  >> `preserves_same_frame prefix` by (
       simp[Abbr`prefix`] >> IF_CASES_TAC >> simp[])
  >> Cases_on `prefix s`
  >> qmatch_asmsub_rename_tac `prefix s = (res, sp)`
  >> `same_frame_rel s sp` by metis_tac[preserves_same_frame_def]
  >> `LENGTH sp.contexts = LENGTH s.contexts` by fs[same_frame_rel_def]
  >> `sp.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
  >> reverse (Cases_on `res`) >> simp[]
  >- (strip_tac >> gvs[])
  >> simp[Once bind_def, get_num_contexts_def, return_def]
  >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[])
  >> simp[Once bind_def]
  >> simp[get_return_data_def, bind_def, get_current_context_def,
          return_def, fail_def]
  >> Cases_on `sp.contexts` >> fs[]
  >> simp[get_output_to_def, bind_def, get_current_context_def,
          return_def, fail_def]
  >> Cases_on `pop_and_incorporate_context (e = NONE) sp` >> simp[]
  >> Cases_on `q'` >> simp[]
  >- ((* INL case: pop succeeded, shrinks by exactly 1. *)
      `LENGTH r.contexts + 1 = LENGTH sp.contexts` by (
        qhdtm_x_assum `pop_and_incorporate_context` mp_tac
        >> gvs[pop_and_incorporate_context_def, bind_def, ignore_bind_def,
               get_gas_left_def, return_def, pop_context_def, fail_def,
               unuse_gas_def, get_current_context_def,
               set_current_context_def, push_logs_def,
               update_gas_refund_def, set_rollback_def, assert_def,
               AllCaseEqs()]
        >> strip_tac >> gvs[] >> pop_assum mp_tac
        >> IF_CASES_TAC
        >> gvs[bind_def, get_current_context_def, set_current_context_def,
               return_def, fail_def, set_rollback_def, AllCaseEqs()]
        >> strip_tac >> gvs[])
      >> simp[inc_pc_def, bind_def, get_current_context_def,
              ignore_bind_def, set_current_context_def]
      >> IF_CASES_TAC >> gvs[return_def, return_destination_CASE_rator]
      >> rw[] >> gvs[AllCaseEqs(),bind_def,COND_RATOR]
      >> gvs[set_return_data_def,push_stack_def,write_memory_def,
             get_current_context_def,bind_def,return_def,fail_def,
             assert_def,pop_and_incorporate_context_def,AllCaseEqs(),
             ignore_bind_def,set_current_context_def])
  (* INR case: pop failed. *)
  >> strip_tac >> gvs[]
  >> gvs[set_return_data_def,push_stack_def,write_memory_def,
         get_current_context_def,bind_def,return_def,fail_def,
         assert_def,pop_and_incorporate_context_def,AllCaseEqs(),
         ignore_bind_def,set_current_context_def,COND_RATOR,
         pop_context_def,unuse_gas_def,push_logs_def,update_gas_refund_def,
         get_gas_left_def,set_rollback_def]
QED

(* handle_create doesn't change contexts length (it may modify
   account.code for Code outputTo success but doesn't touch contexts). *)
Theorem handle_create_preserves_length:
  handle_create e s = (q, s') ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     update_accounts_def, assert_def, set_current_context_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
  >> gvs[AllCaseEqs()]
  >> Cases_on `s.contexts` >> fs[]
QED

(* Generic handle_exception pop structure: when it shrinks, the contexts
   take the form (new_head, SND parent) :: rest with msgParams preserved,
   and the rollback is either s.rollback (success) or callee_rb (failure). *)
Theorem handle_exception_pop_generic_gen:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  handle_exception e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ⇒
    (s'.rollback = s.rollback ∨ s'.rollback = callee_rb) ∧
    ∃new_parent_ctx.
      s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
      new_parent_ctx.msgParams = (FST parent).msgParams
Proof
  strip_tac
  >> Cases_on `parent`
  >> Cases_on `callee.msgParams.outputTo`
  >> Cases_on `e = NONE`
  >> Cases_on `e = SOME Reverted`
  >> gvs[handle_exception_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, pop_context_def,
         set_rollback_def, unuse_gas_def,
         update_gas_refund_def, push_logs_def, AllCaseEqs()]
QED

(* handle_create preserves TL(contexts) and SND(HD contexts).
   For Code+NONE case it modifies HD(contexts) gasUsed; for other
   cases it's an exact reraise. In both sub-cases TL and SND-of-HD
   are unchanged. *)
Theorem handle_create_preserves_tl_and_snd_hd:
  handle_create e s = (q, s') ∧ s.contexts ≠ [] ⇒
    s'.contexts ≠ [] ∧
    TL s'.contexts = TL s.contexts ∧
    SND (HD s'.contexts) = SND (HD s.contexts) ∧
    (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     update_accounts_def, assert_def, set_current_context_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
  >> gvs[AllCaseEqs()]
  >> Cases_on `s.contexts` >> fs[]
QED

(* handle_create preserves rollback (it only modifies .code via
   update_accounts which writes into rollback.accounts). Actually
   update_accounts DOES modify rollback.accounts, so this is FALSE
   in the Code+NONE case. Instead provide a weaker lemma: in the
   cases where handle_create doesn't go into Code+NONE, rollback
   is unchanged. *)
Theorem handle_create_non_code_success_preserves_rollback:
  handle_create e s = (q, s') ∧ s.contexts ≠ [] ∧
  (e ≠ NONE ∨ ∃mr. (FST (HD s.contexts)).msgParams.outputTo = Memory mr) ⇒
  s'.rollback = s.rollback
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     update_accounts_def, assert_def, set_current_context_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
QED

(* handle_create preserves .accesses: all primitives within
   handle_create are either reads, preserves_rollback, or update_accounts
   with a function touching only .accounts (not .accesses). *)
Theorem handle_create_preserves_accesses:
  handle_create e s = (q, s') ⇒
  s'.rollback.accesses = s.rollback.accesses
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     update_accounts_def, assert_def, set_current_context_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
QED

(* Generic handle_step pop structure — storage-aware.

   When handle_step shrinks contexts, the contexts structure is 
   (new_head, SND parent) :: rest, and the storage of s'.rollback.accounts
   equals the storage of either s.rollback.accounts (success pop) OR
   callee_rb.accounts (failure pop) — at every address.

   For Code+NONE+success case, handle_create deposits bytecode before
   pop. This changes .code but not .storage. So the storage equality
   still holds. *)
Theorem handle_step_pop_generic_gen:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  handle_step e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ⇒
    ((∀a. (lookup_account a s'.rollback.accounts).storage =
          (lookup_account a s.rollback.accounts).storage) ∨
     (∀a. (lookup_account a s'.rollback.accounts).storage =
          (lookup_account a callee_rb.accounts).storage)) ∧
    ∃new_parent_ctx.
      s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
      new_parent_ctx.msgParams = (FST parent).msgParams
Proof
  strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def]
  >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[])
  >> simp[handle_def]
  >> `s.contexts ≠ []` by simp[]
  >> drule_then (qspec_then `e` mp_tac)
       (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
  >> strip_tac >> simp[]
  >> qmatch_asmsub_rename_tac `handle_create e s = (INR e', s1)`
  >> drule_all handle_create_preserves_tl_and_snd_hd
  >> strip_tac
  >> `s1.contexts = (FST (HD s1.contexts), callee_rb) :: parent :: rest` by (
       Cases_on `s1.contexts` >> fs[]
       >> PairCases_on `h` >> fs[])
  >> drule_all handle_create_preserves_length
  >> strip_tac
  >> strip_tac
  >> `LENGTH s'.contexts < LENGTH s1.contexts` by decide_tac
  >> drule_all handle_exception_pop_generic_gen
  >> strip_tac >> gvs[]
  >> mp_tac (INST_TYPE[alpha|->``:unit``]preserves_storage_handle_create)
  >> rewrite_tac[preserves_storage_def]
  >> disch_then drule
  >> gvs[lookup_storage_def, FUN_EQ_THM]
QED

(* Strengthening of handle_step_pop_generic_gen that pairs each
   storage disjunct with the matching accesses subset. *)
Theorem handle_step_pop_generic_gen_paired:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  handle_step e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ⇒
    ∃new_parent_ctx.
      s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
      new_parent_ctx.msgParams = (FST parent).msgParams ∧
      ((toSet s.rollback.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a s.rollback.accounts).storage)) ∨
       (toSet callee_rb.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a callee_rb.accounts).storage)))
Proof
  strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def]
  >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[])
  >> simp[handle_def]
  >> `s.contexts ≠ []` by simp[]
  >> drule_then (qspec_then `e` mp_tac)
       (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
  >> strip_tac >> simp[]
  >> qmatch_asmsub_rename_tac `handle_create e s = (INR e', s1)`
  >> drule_all handle_create_preserves_tl_and_snd_hd
  >> strip_tac
  >> `s1.contexts = (FST (HD s1.contexts), callee_rb) :: parent :: rest` by (
       Cases_on `s1.contexts` >> fs[]
       >> PairCases_on `h` >> fs[])
  >> drule_all handle_create_preserves_length
  >> strip_tac
  >> strip_tac
  >> `LENGTH s'.contexts < LENGTH s1.contexts` by decide_tac
  >> drule_all handle_exception_pop_generic_gen
  >> strip_tac >> gvs[]
  >> drule handle_create_preserves_accesses
  >> mp_tac (INST_TYPE[alpha|->``:unit``]preserves_storage_handle_create)
  >> rewrite_tac[preserves_storage_def]
  >> disch_then drule
  >> gvs[lookup_storage_def, FUN_EQ_THM]
QED

(* Saved rollback's accesses are in s'.rollback's accesses, regardless
   of which pop branch handle_step took.
   Requires the hypothesis callee_rb.accesses ⊆ s.rollback.accesses
   (a structural invariant: at push_context time the saved rollback
   equals current, and accesses only grow). This invariant needs to
   be added to run_call_inv as:
     EVERY (λrb. toSet rb.accesses.storageKeys ⊆
                 toSet s.rollback.accesses.storageKeys)
           (MAP SND s.contexts)
   and maintained by run_call_inv_step. *)
Theorem handle_step_pop_accesses_bound:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  handle_step e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ∧
  toSet callee_rb.accesses.storageKeys ⊆
    toSet s.rollback.accesses.storageKeys ⇒
  toSet callee_rb.accesses.storageKeys ⊆
    toSet s'.rollback.accesses.storageKeys
Proof
  rw[] >>
  drule_then drule handle_step_pop_generic_gen_paired >>
  rw[] >>
  gvs[SUBSET_DEF]
QED

Theorem handle_step_preserves_length_1:
  handle_step e s = (q, s') ∧ LENGTH s.contexts = 1 ⇒
  LENGTH s'.contexts = 1
Proof
  strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def]
  >> reverse IF_CASES_TAC >> simp[]
  >> TRY (simp[reraise_def] >> strip_tac >> gvs[] >> NO_TAC)
  >> simp[handle_def]
  >> `s.contexts ≠ []` by (Cases_on `s.contexts` >> fs[])
  >> drule_then (qspec_then `e` mp_tac)
       (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
  >> strip_tac >> simp[]
  >> qmatch_asmsub_rename_tac `handle_create e s = (INR e', s1)`
  >> drule_all handle_create_preserves_length
  >> strip_tac
  >> `LENGTH s1.contexts = 1` by simp[]
  >> simp[Once handle_exception_def]
  >> simp[ignore_bind_def, Once bind_def]
  >> qmatch_goalsub_abbrev_tac `pair_CASE (prefix s1)`
  >> `preserves_same_frame prefix` by (
       simp[Abbr`prefix`]
       >> IF_CASES_TAC >> simp[]
       >> irule preserves_same_frame_ignore_bind >> simp[]
       >> irule preserves_same_frame_bind >> simp[])
  >> Cases_on `prefix s1`
  >> qmatch_asmsub_rename_tac `prefix s1 = (res, sp)`
  >> `s1.contexts ≠ []` by (Cases_on `s1.contexts` >> fs[])
  >> `same_frame_rel s1 sp` by (
       Cases_on `res` >> metis_tac[preserves_same_frame_def])
  >> `LENGTH sp.contexts = 1` by fs[same_frame_rel_def]
  >> reverse (Cases_on `res`) >> simp[]
  >- (strip_tac >> gvs[])
  >> simp[Once bind_def, get_num_contexts_def, return_def]
  >> simp[reraise_def]
  >> strip_tac >> gvs[]
QED

(* handle_step reduces contexts by at most one. *)
Theorem handle_step_shrinks_by_one:
  handle_step e s = (q, s') ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts + 1 ≥ LENGTH s.contexts ∧
  LENGTH s'.contexts ≤ LENGTH s.contexts
Proof
  strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def]
  >> reverse IF_CASES_TAC >> simp[]
  >> TRY (strip_tac >> gvs[reraise_def] >> NO_TAC)
  >> simp[handle_def]
  >> drule_then (qspec_then `e` mp_tac)
       (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
  >> strip_tac
  >> simp[]
  >> qmatch_asmsub_rename_tac `handle_create e s = (INR e', s1)`
  >> drule_all handle_create_preserves_length
  >> strip_tac
  >> `s1.contexts ≠ []` by (Cases_on `s1.contexts` >> fs[])
  >> strip_tac
  >> imp_res_tac handle_exception_shrinks_by_one
  >> fs[]
QED

(* Unfold step = handle inner handle_step. For the same_frame case,
   we have four sub-cases to analyse:
     (A) inner INL, no-grow → step s = inner s with s' = inner's s'.
     (B) inner INR, no-grow → handle_step reraised, s' = inner's s'.
     (C) inner INL, grew → contradicts same_frame (can't happen).
     (D) inner INR, grew + handle_step popped.
   Cases (A) and (B) reduce to step_inst behavior, where
   step_inst_preserves_non_accessed_storage applies.
   Case (C) is vacuous.
   Case (D) requires push structure. *)
Theorem step_preserves_non_accessed_storage:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent s ∧
    same_frame_rel s s' ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >> reverse (Cases_on `a = (FST (HD s.contexts)).msgParams.callee`)
  >- (
    (* Non-callee address: callee_local_changes gives equality directly. *)
    `(lookup_account a s'.rollback.accounts).storage =
     (lookup_account a s.rollback.accounts).storage`
       by fs[same_frame_rel_def, callee_local_changes_def]
    >> simp[])
  (* Callee address. Unfold step = handle inner handle_step and
     analyse the cases. *)
  >> `¬fIN (SK a k) s.rollback.accesses.storageKeys` by (
       `toSet s.rollback.accesses.storageKeys ⊆
        toSet s'.rollback.accesses.storageKeys`
          by fs[same_frame_rel_def]
       >> fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
       >> metis_tac[])
  (* Unfold step = handle inner handle_step. *)
  >> qhdtm_x_assum `step` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `pair_CASE (inner s)`
  >> `same_frame_or_grow inner` by simp[Abbr`inner`]
  >> Cases_on `inner s` >> Cases_on `q` >> simp[]
  >- (
    (* inner INL: step returns inner result. *)
    strip_tac >> gvs[]
    (* Unfold inner to get the actual primitives that ran. *)
    >> qhdtm_x_assum `Abbrev` mp_tac
    >> simp[markerTheory.Abbrev_def]
    >> disch_then SUBST_ALL_TAC
    >> qpat_x_assum `_ s = (INL (), r')` mp_tac
    >> simp[bind_def, ignore_bind_def]
    >> simp[get_current_context_def, return_def, fail_def]
    >> Cases_on `s.contexts` >> gvs[]
    >> Cases_on `LENGTH (FST h).msgParams.code ≤ (FST h).pc` >> gvs[]
    >- (
      (* Stop case. *)
      strip_tac
      >> drule step_inst_preserves_non_accessed_storage
      >> simp[is_call_def]
      >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
      >> simp[])
    >> Cases_on `FLOOKUP (FST h).msgParams.parsed (FST h).pc` >> gvs[]
    >- (
      (* Invalid case. *)
      strip_tac
      >> drule step_inst_preserves_non_accessed_storage
      >> simp[is_call_def]
      >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
      >> simp[])
    (* SOME op: step_inst op; inc_pc_or_jump op. *)
    >> strip_tac
    >> gvs[bind_def, ignore_bind_def, AllCaseEqs()]
    >> rename1 `step_inst op s = (INL _, r_mid)`
    >> `r_mid.rollback = r'.rollback`
         by (mp_tac preserves_rollback_inc_pc_or_jump
             >> rewrite_tac[preserves_rollback_def]
             >> disch_then drule
             >> simp[])
    >> `s.contexts ≠ []` by (strip_tac >> fs[])
    >> Cases_on `is_call op`
    >- (
      (* Call/Create family: step_inst returned INL with same frame length
         (since inc_pc_or_jump is same_frame and r' has same length as s).
         This means an abort path ran — no storage written. *)
      `r_mid.contexts ≠ []` by (
         `(SND (step_inst op s)).contexts ≠ []`
            by metis_tac[step_inst_preserves_nonempty_contexts]
         >> rev_full_simp_tac std_ss [])
      >> `LENGTH r_mid.contexts = LENGTH s.contexts` by (
         `LENGTH r'.contexts = LENGTH r_mid.contexts` by (
            `preserves_same_frame (inc_pc_or_jump op)` by simp[]
            >> metis_tac[psf_imp_length_contexts_preserved])
         >> fs[same_frame_rel_def])
      >> drule_all is_call_same_frame_preserves_storage
      >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
      >> simp[])
    >> drule step_inst_preserves_non_accessed_storage
    >> simp[]
    >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
    >> simp[])
  >> strip_tac >>
  qhdtm_x_assum`same_frame_or_grow`mp_tac >>
  simp[same_frame_or_grow_def] >> disch_then drule >> simp[] >>
  strip_tac >- (
    qpat_x_assum`inner _ = _`mp_tac >>
    simp[Abbr`inner`, bind_def,AllCaseEqs()] >>
    simp[get_current_context_def, return_def, COND_RATOR, AllCaseEqs()] >>
    strip_tac >- (
      drule step_inst_preserves_non_accessed_storage >>
      simp[is_call_def] >>
      disch_then(qspecl_then[`a`,`k`]mp_tac) >>
      impl_keep_tac >- (
        gvs[step_inst_def, bind_def, ignore_bind_def,
            set_return_data_def, finish_def, AllCaseEqs(),
            get_current_context_def,set_current_context_def,
            return_def,fail_def] ) >>
      disch_then $ assume_tac o SYM >> gvs[] >>
      irule handle_step_preserves_storage_same_length >>
      drule same_frame_rel_contexts_ne >> simp[] >> strip_tac >>
      conj_asm1_tac >- (
        gvs[same_frame_rel_def] >>
        gvs[outputTo_consistent_def] ) >>
      reverse conj_tac >- goal_assum drule >>
      fs[same_frame_rel_def] ) >>
    gvs[AllCaseEqs(),option_CASE_rator] >- (
      drule step_inst_preserves_non_accessed_storage >>
      simp[is_call_def] >>
      qmatch_goalsub_abbrev_tac`lookup_account a` >>
      disch_then(qspecl_then[`a`,`k`]mp_tac) >>
      impl_keep_tac >- (
        gvs[step_inst_def, bind_def, ignore_bind_def,
            set_return_data_def, finish_def, AllCaseEqs(),
            get_current_context_def,set_current_context_def,
            return_def,fail_def] ) >>
      disch_then $ assume_tac o SYM >> gvs[] >>
      irule handle_step_preserves_storage_same_length >>
      drule same_frame_rel_contexts_ne >> simp[] >> strip_tac >>
      conj_asm1_tac >- (
        gvs[same_frame_rel_def] >>
        gvs[outputTo_consistent_def] ) >>
      reverse conj_tac >- goal_assum drule >>
      fs[same_frame_rel_def] ) >>
    pop_assum mp_tac >>
    simp[ignore_bind_def,bind_def] >>
    TOP_CASE_TAC >> strip_tac >>
    reverse (Cases_on `q`) >> gvs[] >- (
      (* step_inst op s = (INR y, r' = r'') *)
      Cases_on `is_call op` >- (
        (* call op INR same-length: use preserves_storage_step_call/create *)
        `lookup_storage k
            (lookup_account (FST (HD s.contexts)).msgParams.callee
               r'.rollback.accounts).storage =
         lookup_storage k
            (lookup_account (FST (HD s.contexts)).msgParams.callee
               s.rollback.accounts).storage` by (
          Cases_on `op` >> fs[is_call_def, step_inst_def]
          >> metis_tac[preserves_storage_step_call, preserves_storage_step_create,
                       preserves_storage_def])
        >> irule EQ_TRANS
        >> qexists `lookup_storage k
                      (lookup_account (FST (HD s.contexts)).msgParams.callee
                         r'.rollback.accounts).storage`
        >> reverse conj_tac >- metis_tac[]
        >> irule handle_step_preserves_storage_same_length
        >> drule same_frame_rel_contexts_ne >> simp[] >> strip_tac
        >> conj_asm1_tac >- (gvs[same_frame_rel_def] >> gvs[outputTo_consistent_def])
        >> reverse conj_tac >- goal_assum drule
        >> fs[same_frame_rel_def])
      >> (* non-call op *)
         `outputTo_consistent r'` by (
           fs[outputTo_consistent_def]
           >> `r'.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
           >> `(FST (HD r'.contexts)).msgParams = (FST (HD s.contexts)).msgParams`
                by fs[same_frame_rel_def]
           >> simp[])
         >> `LENGTH s'.contexts = LENGTH r'.contexts` by fs[same_frame_rel_def]
         >> `same_frame_rel r' s'` by metis_tac[handle_step_same_frame]
         >> drule step_inst_preserves_non_accessed_storage >> simp[]
         >> disch_then (qspecl_then [`(FST (HD s.contexts)).msgParams.callee`, `k`] mp_tac)
         >> impl_keep_tac
         >- (`toSet r'.rollback.accesses.storageKeys ⊆
              toSet s'.rollback.accesses.storageKeys`
               by fs[same_frame_rel_def]
             >> fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
             >> metis_tac[])
         >> strip_tac
         >> pop_assum $ assume_tac o SYM >> gvs[]
         >> irule handle_step_preserves_storage_same_length
         >> drule same_frame_rel_contexts_ne >> simp[] >> strip_tac
         >> reverse conj_tac >- goal_assum drule
         >> imp_res_tac same_frame_rel_contexts_ne)
    >> (* step_inst op s = (INL x, r''), inc_pc_or_jump op r'' = (INR y, r').
          Jump ops can fail with InvalidJumpDest. We handle this by first
          using step_inst_preserves_non_accessed_storage on s → r''
          (for non-call ops), then inc_pc_or_jump preserves rollback
          (storage and accesses unchanged), so r' ≡ r'' on rollback. *)
       Cases_on `is_call op`
       >- ((* is_call op + step_inst INL + inc_pc_or_jump INR: impossible.
              For is_call op, inc_pc_or_jump op = return () which always
              returns (INL (), r). So INR is impossible. *)
           fs[inc_pc_or_jump_def, return_def])
       >> (* non-call op case *)
          `outputTo_consistent r'` by (
            fs[outputTo_consistent_def]
            >> `r'.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
            >> `(FST (HD r'.contexts)).msgParams = (FST (HD s.contexts)).msgParams`
                 by fs[same_frame_rel_def]
            >> simp[])
          >> `LENGTH s'.contexts = LENGTH r'.contexts` by fs[same_frame_rel_def]
          >> `same_frame_rel r' s'` by metis_tac[handle_step_same_frame]
          >> `lookup_storage k
                (lookup_account (FST (HD s.contexts)).msgParams.callee
                   r'.rollback.accounts).storage =
              lookup_storage k
                (lookup_account (FST (HD s.contexts)).msgParams.callee
                   s.rollback.accounts).storage` by (
             (* Chain: s → r'' (step_inst) → r' (inc_pc_or_jump).
                inc_pc_or_jump preserves_rollback, so r'.rollback = r''.rollback.
                step_inst_preserves_non_accessed_storage gives storage r'' = storage s
                at non-accessed slots. *)
             qhdtm_x_assum `step_inst` assume_tac
             >> drule step_inst_preserves_non_accessed_storage
             >> simp[]
             >> disch_then (qspecl_then
                 [`(FST (HD s.contexts)).msgParams.callee`, `k`] mp_tac)
             >> `r'.rollback = r''.rollback` by (
                mp_tac preserves_rollback_inc_pc_or_jump
                >> rewrite_tac[preserves_rollback_def]
                >> disch_then drule >> simp[])
             >> fs[]
             >> impl_tac
             >- (`toSet r''.rollback.accesses.storageKeys ⊆
                  toSet s'.rollback.accesses.storageKeys`
                    by (`r''.rollback = r'.rollback` by simp[]
                        >> fs[same_frame_rel_def])
                 >> fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
                 >> metis_tac[])
             >> strip_tac >> fs[])
          >> pop_assum $ assume_tac o SYM >> gvs[]
          >> irule handle_step_preserves_storage_same_length
          >> simp[]
          >> reverse conj_tac >- goal_assum drule
          >> imp_res_tac same_frame_rel_contexts_ne) >>
  `LENGTH s'.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def] >>
  gvs[Abbr`inner`,bind_def,AllCaseEqs(),get_current_context_def,return_def] >>
  gvs[COND_RATOR,AllCaseEqs()] >- (
    `¬is_call Stop` by simp[is_call_def] >>
    drule preserves_same_frame_step_inst_not_call >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    simp[same_frame_rel_def] ) >>
  gvs[option_CASE_rator,AllCaseEqs()] >- (
    `¬is_call Invalid` by simp[is_call_def] >>
    drule preserves_same_frame_step_inst_not_call >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    simp[same_frame_rel_def] ) >>
  qpat_x_assum`_ = (INR _, _)`mp_tac >>
  simp[ignore_bind_def,bind_def] >> TOP_CASE_TAC >>
  reverse $ Cases_on`is_call op` >- (
    drule preserves_same_frame_step_inst_not_call >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    simp[same_frame_rel_def] >> strip_tac >>
    CASE_TAC >> rw[] >> gvs[] >>
    mp_tac preserves_same_frame_inc_pc_or_jump >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    rw[same_frame_rel_def] >> gvs[] ) >>
  simp[inc_pc_or_jump_def, return_def] >>
  TOP_CASE_TAC >> rw[] >>
  drule_at Any handle_step_pop_generic_gen >>
  Cases_on`r'.contexts` >> gvs[] >>
  Cases_on`h` >> gvs[] >>
  Cases_on`t` >> gvs[] >- ( Cases_on`s.contexts` >> gvs[] ) >>
  disch_then assume_tac >>
  irule EQ_TRANS >>
  qmatch_goalsub_abbrev_tac`lookup_storage k (lookup_account a _).storage` >>
  qexists_tac`lookup_storage k (lookup_account a r'.rollback.accounts).storage` >>
  reverse conj_tac >- (
    qpat_x_assum`_ ∧ _`kall_tac >>
    mp_tac (INST_TYPE[alpha |-> ``:unit``](GEN_ALL preserves_storage_step_call)) >>
    mp_tac (INST_TYPE[alpha |-> ``:unit``](GEN_ALL preserves_storage_step_create)) >>
    rewrite_tac[preserves_storage_def] >>
    Cases_on`op` >> gvs[is_call_def, step_inst_def] >>
    rpt strip_tac >> first_x_assum drule >> rw[] ) >>
  (* Now prove: storage s'.rollback @ a,k = storage r'.rollback @ a,k.
     From handle_step_pop_generic_gen disjunction:
       (A) ∀a. storage s'.rollback @ a = storage r'.rollback @ a, OR
       (B) ∀a. storage s'.rollback @ a = storage r''.accounts @ a
     where SND (HD r'.contexts) = r''.
     For (A): direct.
     For (B): use step_call_pushed_rb_storage (or step_create variant)
     to get storage r''.accounts @ a = storage s.rollback @ a, then
     chain via preserves_storage_step_call/create to relate s.rollback
     to r'.rollback. *)
  qpat_x_assum `_ ∧ _` strip_assume_tac
  (* strip_assume_tac splits the conjunction AND the inner disjunction,
     producing 2 subgoals — one per disjunct from handle_step_pop_generic_gen. *)
  >- ((* Disjunct A: ∀a. storage s'.rollback @ a = storage r'.rollback @ a. *)
      simp[] >> metis_tac[])
  (* Disjunct B: ∀a. storage s'.rollback @ a = storage r''.accounts @ a.
     Here r'' = SND (HD r'.contexts). Chain:
       storage s'.rollback @ a = storage r''.accounts @ a (hypothesis)
                             = storage s.rollback @ a  (step_call_pushed_rb_storage)
                             = storage r'.rollback @ a (preserves_storage step_inst) *)
  >> `(lookup_account a r''.accounts).storage =
      (lookup_account a s.rollback.accounts).storage` by (
       `LENGTH r'.contexts > LENGTH s.contexts` by simp[]
       >> `SND (HD r'.contexts) = r''` by simp[]
       >> Cases_on `op` >> fs[is_call_def, step_inst_def]
       >> metis_tac[step_call_pushed_rb_storage,
                    step_create_pushed_rb_storage])
  >> `lookup_storage k (lookup_account a s.rollback.accounts).storage =
      lookup_storage k (lookup_account a r'.rollback.accounts).storage` by (
       Cases_on `op` >> fs[is_call_def, step_inst_def]
       >> metis_tac[preserves_storage_step_call, preserves_storage_step_create,
                    preserves_storage_def])
  >> `lookup_storage k (lookup_account a s'.rollback.accounts).storage =
      lookup_storage k (lookup_account a r''.accounts).storage` by simp[]
  >> simp[]
  (*
 6. Second disjunct needs a new helper: step_call_saved_rollback_preserves_storage / step_call_saved_rollback_preserves_storage_create — if is_call op ∧
 step_inst op s = (q, r') ∧ LENGTH r'.contexts = LENGTH s.contexts + 1, then the top saved rollback SND (HD r'.contexts) has the same storage as s.rollback at
 every (a,k). Proof: push_context stores the then-current rollback; all step_call/create primitives before push_context are preserves_storage, so rollback
 storage at push-time equals at entry; after push_context, further ops (none, or only reraise-like) don't touch SND (HD · contexts). Close by the same
 bind-decomposition pattern as preserves_storage_step_call, but tracking SND (HD (s'.contexts)) instead of s'.rollback.
 *)
QED

(* -------------------------------------------------------------------------
 * Push-structure lemma for step (Case +1 of run_call_inv_step).
 *
 * When step grows by +1 (push), the new contexts prepend a child context
 * with a pushed rollback. The prior parent context may have been modified
 * (gasUsed/stack updated by consume_gas/pop_stack in the step_call prefix),
 * but its SND component (saved rollback) is unchanged and its .msgParams
 * is unchanged (modifications via set_current_context preserve both).
 *
 * The pushed rollback's .accounts.storage equals s.rollback.accounts.storage
 * (via step_call_pushed_rb_storage / step_create_pushed_rb_storage).
 * The new s'.rollback.accounts.storage also equals s.rollback.accounts.storage
 * (the only modifications during push prefix are transfer_value and
 * increment_nonce, both of which preserve storage).
 *
 * Accesses are monotone.
 *
 * Covers both:
 *   - INL-grow: plain proceed_call or proceed_create success (no precompile).
 *   - INR-grow: step_call INR-grew with vfm_abort e (handle_step reraised).
 *     (step_create never INR-grows, per step_create_inr_no_grow.)
 * ------------------------------------------------------------------------- *)
(* INL-grow structure framework. Mirrors the inr_grow_witness framework
   from vfmRunWithinFrame, but for INL-grow (the normal case where
   step_call returns INL and contexts grow by 1). *)

(* bind_inl_grow_factor: peel off a preserves_same_frame prefix from
   an INL-growing bind chain. If g preserves_same_frame and bind g f
   returns INL with contexts growing, then g must have returned INL
   (otherwise same_frame gives equal lengths, contradicting growth),
   and f produced the growth. *)
Theorem bind_inl_grow_factor:
  preserves_same_frame g ∧
  bind g f s = (INL x, s1) ∧
  s.contexts ≠ [] ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ∃y sp. g s = (INL y, sp) ∧ same_frame_rel s sp ∧ f y sp = (INL x, s1)
Proof
  strip_tac
  >> fs[preserves_same_frame_def]
  >> `∀rr ss. g s = (rr, ss) ⇒ same_frame_rel s ss`
      by (rpt strip_tac >> first_x_assum drule >> simp[])
  >> Cases_on `g s`
  >> rename1 `g s = (q, sp)`
  >> Cases_on `q`
  >- (
    qexists_tac `x'` >> qexists_tac `sp`
    >> `same_frame_rel s sp` by (first_x_assum irule >> simp[])
    >> simp[]
    >> qpat_x_assum `monad_bind _ _ _ = _` mp_tac
    >> simp[bind_def])
  >> `same_frame_rel s sp` by (first_x_assum irule >> simp[])
  >> qpat_x_assum `monad_bind _ _ _ = _` mp_tac
  >> simp[bind_def]
  >> spose_not_then strip_assume_tac
  >> fs[same_frame_rel_def]
QED

Theorem ignore_bind_inl_grow_factor:
  preserves_same_frame g ∧
  ignore_bind g f s = (INL (), s1) ∧
  s.contexts ≠ [] ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ∃sp. g s = (INL (), sp) ∧ same_frame_rel s sp ∧ f sp = (INL (), s1)
Proof
  rw[ignore_bind_def]
  >> drule_all bind_inl_grow_factor
  >> rw[]
QED

Definition inl_grow_structure_def:
  inl_grow_structure (m : α execution) ⇔
    ∀s r s'. m s = (INL r, s') ∧ s.contexts ≠ [] ∧
             LENGTH s'.contexts > LENGTH s.contexts ⇒
      ∃callee_ctx pushed_rb parent_ctx.
        s'.contexts = (callee_ctx, pushed_rb) ::
                      (parent_ctx, SND (HD s.contexts)) ::
                      TL s.contexts ∧
        parent_ctx.msgParams = (FST (HD s.contexts)).msgParams ∧
        (∀a. (lookup_account a pushed_rb.accounts).storage =
             (lookup_account a s.rollback.accounts).storage) ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a s.rollback.accounts).storage) ∧
        toSet s.rollback.accesses.storageKeys ⊆
          toSet pushed_rb.accesses.storageKeys ∧
        toSet s.rollback.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        outputTo_consistent_ctx callee_ctx
End

Theorem inl_grow_structure_of_same_frame[simp]:
  preserves_same_frame m ⇒ inl_grow_structure m
Proof
  rw[inl_grow_structure_def, preserves_same_frame_def]
  >> first_x_assum drule >> simp[same_frame_rel_def]
QED

Theorem inl_grow_structure_bind:
  preserves_same_frame g ∧ preserves_storage g ∧
  (∀x. inl_grow_structure (f x)) ⇒
  inl_grow_structure (bind g f)
Proof
  rw[inl_grow_structure_def, bind_def] >> gvs[AllCaseEqs()] >>
  fs[preserves_storage_def, preserves_same_frame_def] >>
  qpat_x_assum `∀s r s'. g s = (r,s') ∧ s.contexts ≠ [] ⇒ same_frame_rel s s'`
    (qspecl_then [`s`,`INL x`,`s''`] mp_tac) >> simp[] >> disch_tac >>
  `s''.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne] >>
  `LENGTH s'.contexts > LENGTH s''.contexts` by
    (fs[same_frame_rel_def] >> decide_tac) >>
  first_x_assum (qspecl_then [`x`,`s''`,`r`,`s'`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists `callee_ctx` >> qexists `pushed_rb` >> qexists `parent_ctx` >>
  gvs[same_frame_rel_def] >>
  rpt conj_tac >-
    (* storage equality: preserves_storage gives lookup_storage eq, then FUN_EQ_THM *)
    (gen_tac >>
     qpat_x_assum `∀s r s'. g s = (r,s') ⇒ _`
       (qspecl_then [`s`,`INL x`,`s''`] mp_tac) >> simp[] >>
     disch_then (qspec_then `a` mp_tac) >>
     simp[lookup_storage_def, FUN_EQ_THM]) >-
    (* same for second copy *)
    (gen_tac >>
     qpat_x_assum `∀s r s'. g s = (r,s') ⇒ _`
       (qspecl_then [`s`,`INL x`,`s''`] mp_tac) >> simp[] >>
     disch_then (qspec_then `a` mp_tac) >>
     simp[lookup_storage_def, FUN_EQ_THM]) >-
    (* s ⊆ pushed_rb: SUBSET_TRANS with s ⊆ s'' and s'' ⊆ pushed_rb *)
    metis_tac[SUBSET_TRANS] >-
    (* s ⊆ s': SUBSET_TRANS with s ⊆ s'' and s'' ⊆ s' *)
    metis_tac[SUBSET_TRANS]
QED

Theorem inl_grow_structure_ignore_bind:
  preserves_same_frame g ∧ preserves_storage g ∧
  inl_grow_structure f ⇒
  inl_grow_structure (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule inl_grow_structure_bind >> rw[]
QED

Theorem inl_grow_structure_cond[simp]:
  inl_grow_structure m1 ∧ inl_grow_structure m2 ⇒
  inl_grow_structure (if b then m1 else m2)
Proof
  rw[]
QED

Theorem inl_grow_structure_case_option[simp]:
  inl_grow_structure m_none ∧ (∀x. inl_grow_structure (m_some x)) ⇒
  inl_grow_structure (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem inl_grow_structure_let[simp]:
  (∀x. inl_grow_structure (f x)) ⇒
  inl_grow_structure (let x = v in f x)
Proof
  rw[]
QED

Theorem inl_grow_structure_case_pair[simp]:
  (∀a b. inl_grow_structure (f a b)) ⇒
  inl_grow_structure (case p of (a, b) => f a b)
Proof
  Cases_on `p` >> rw[]
QED

Theorem inl_grow_structure_proceed_call[simp]:
  inl_grow_structure
    (proceed_call op sender address value argsOffset argsSize
                  code stipend (Memory mr))
Proof
  rw[inl_grow_structure_def]
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def]
  >> simp[bind_def, get_rollback_def, return_def]
  >> simp[read_memory_def, bind_def, return_def, get_current_context_def]
  >> qmatch_goalsub_abbrev_tac `ignore_bind g`
  >> simp[ignore_bind_def, Once bind_def]
  >> TOP_CASE_TAC
  >> qmatch_asmsub_rename_tac `g s = (q, s1)`
  >> `∀a. (lookup_account a s1.rollback.accounts).storage =
         (lookup_account a s.rollback.accounts).storage`
      by (`preserves_storage g`
            by (simp[Abbr`g`] >> IF_CASES_TAC >> simp[])
          >> fs[preserves_storage_def] >> first_x_assum drule >>
          rw[lookup_storage_def] >> gvs[FUN_EQ_THM])
  >> `ISL q` by (gvs[Abbr`g`,AllCaseEqs(),COND_RATOR,return_def,
                     update_accounts_def])
  >> Cases_on `q` >> fs[]
  >> `preserves_same_frame g`
       by (Cases_on `op ≠ CallCode ∧ 0 < value`
           >- (simp[Once (Abbr `g`), preserves_same_frame_eq_psf_T,
                    psf_update_accounts_transfer_value])
           >- (simp[Once (Abbr `g`), preserves_same_frame_return]))
  >> `same_frame_rel s s1` by (
    pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> rw[] )
  >> `s1.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
  >> simp[Once bind_def, get_caller_def, return_def, get_current_context_def, fail_def]
  >> simp[Once bind_def, return_def, get_current_context_def, fail_def]
  >> simp[Once bind_def, return_def, get_current_context_def, fail_def]
  >> simp[Once bind_def, return_def, get_current_context_def, fail_def]
  >> simp[Once bind_def, return_def]
  >> simp[Once bind_def, return_def]
  >> simp[Once bind_def, get_value_def, return_def, get_current_context_def, fail_def]
  >> simp[Once bind_def, return_def, get_current_context_def, fail_def]
  >> simp[Once bind_def, return_def]
  >> simp[Once bind_def, get_static_def, return_def, get_current_context_def, fail_def]
  >> simp[Once bind_def, return_def, get_current_context_def, fail_def]
  >> simp[Once bind_def, return_def]
  >> simp[Once bind_def, return_def]
  >> simp[Once bind_def]
  >> TOP_CASE_TAC
  >> reverse IF_CASES_TAC
  >- ((* No precompile *)
       drule push_context_effect >> strip_tac
       >> gvs[return_def]
       >> strip_tac >> gvs[]
       >> qmatch_asmsub_abbrev_tac `push_context (ctx, _) s1`
       >> simp[initial_context_simp, initial_msg_params_def]
       >> simp[outputTo_consistent_ctx_def]
       >> gvs[Abbr`g`,COND_RATOR,CaseEq"bool",return_def,update_accounts_def]
       >> Cases_on`s.contexts` >> gvs[]
       >> Cases_on`h` >> gvs[]
       >> gvs[Abbr`ctx`, initial_context_simp, initial_msg_params_def] )
  >> drule push_context_effect >> strip_tac >> gvs[]
  >> qmatch_asmsub_abbrev_tac `push_context (ctx, _) s1`
  >> strip_tac
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles addr ss = (_,s')`
  >> `ss.contexts ≠ []` by simp[Abbr`ss`]
  >> qmatch_asmsub_abbrev_tac `dpa ss = (_,_)`
  >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
  >> `preserves_storage dpa` by (simp[Abbr`dpa`] >>
        simp[preserves_rollback_dispatch_precompiles, preserves_rollback_imp_preserves_storage])
  >> ntac 2 $ pop_assum mp_tac
  >> rewrite_tac[preserves_same_frame_def, preserves_storage_def]
  >> disch_then drule
  >> `ss.contexts = (ctx,s.rollback) :: s1.contexts` by simp[Abbr`ss`]
  >> strip_tac
  >> disch_then drule
  >> strip_tac
  >> gvs[Abbr`ss`]
  >> gvs[same_frame_rel_def]
  >> gvs[lookup_storage_def, FUN_EQ_THM]
  >> Cases_on`s'.contexts` >> gvs[]
  >> Cases_on`h` >> gvs[]
  >> gvs[SUBSET_DEF]
  >> Cases_on`s1.contexts` >> gvs[]
  >> Cases_on`h` >> gvs[]
  >> simp[initial_context_simp,Abbr`ctx`]
  >> gvs[initial_msg_params_def]
  >> gvs[outputTo_consistent_ctx_def]
QED

Theorem inl_grow_structure_step_call[simp]:
  inl_grow_structure (step_call op)
Proof
  simp[step_call_def]
  >> irule inl_grow_structure_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule inl_grow_structure_bind >> simp[] >> gen_tac
  >> irule inl_grow_structure_bind >> simp[] >> gen_tac
  >> irule inl_grow_structure_bind >> simp[] >> gen_tac
  >> irule inl_grow_structure_bind >> simp[]
  >> reverse conj_tac >- (CASE_TAC >> simp[])
  >> Cases >> simp[]
  >> irule inl_grow_structure_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule inl_grow_structure_ignore_bind >> simp[]
  >> irule inl_grow_structure_ignore_bind >> simp[]
  >> irule inl_grow_structure_ignore_bind >> simp[]
  >> irule inl_grow_structure_bind >> simp[] >> gen_tac
  >> irule inl_grow_structure_cond >> simp[]
  >> irule inl_grow_structure_ignore_bind >> simp[]
  >> irule inl_grow_structure_bind >> simp[] >> gen_tac
  >> irule inl_grow_structure_cond >> simp[]
QED

Theorem step_call_inl_grow_structure:
  s.contexts ≠ [] ∧ outputTo_consistent s ∧
  step_call op s = (INL (), s1) ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ∃callee_ctx pushed_rb parent_ctx.
      s1.contexts = (callee_ctx, pushed_rb) ::
                    (parent_ctx, SND (HD s.contexts)) ::
                    TL s.contexts ∧
      parent_ctx.msgParams = (FST (HD s.contexts)).msgParams ∧
      (∀a. (lookup_account a pushed_rb.accounts).storage =
           (lookup_account a s.rollback.accounts).storage) ∧
      (∀a. (lookup_account a s1.rollback.accounts).storage =
           (lookup_account a s.rollback.accounts).storage) ∧
      toSet s.rollback.accesses.storageKeys ⊆
        toSet pushed_rb.accesses.storageKeys ∧
      toSet s.rollback.accesses.storageKeys ⊆
        toSet s1.rollback.accesses.storageKeys ∧
      outputTo_consistent_ctx callee_ctx
Proof
  strip_tac >>
  mp_tac inl_grow_structure_step_call >>
  rewrite_tac[inl_grow_structure_def, outputTo_consistent_ctx_def] >>
  disch_then drule >> simp[]
QED

(* TODO: move *)
Theorem transfer_value_storage[simp]:
  (transfer_value fr to va ac a).storage = (ac a).storage
Proof
  rw[transfer_value_def, lookup_account_def, update_account_def,
     APPLY_UPDATE_THM] >> rw[]
QED

Theorem increment_nonce_storage[simp]:
  ((increment_nonce x ac) a).storage = (ac a).storage
Proof
  rw[increment_nonce_def, lookup_account_def, update_account_def,
     APPLY_UPDATE_THM] >> rw[]
QED

Theorem inl_grow_structure_proceed_create[simp]:
  inl_grow_structure
    (proceed_create senderAddress address value code cappedGas)
Proof
  rw[inl_grow_structure_def, outputTo_consistent_ctx_def]
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def]
  (* update_accounts (increment_nonce senderAddress) — ignore_bind *)
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  (* get_rollback: captures the rollback after increment_nonce *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  (* get_original *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  (* set_original = bind get_current_context (\c. set_current_context (...)) *)
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def,
          get_current_context_def, set_current_context_def]
  >> gvs[AllCaseEqs()]
  >> TRY (strip_tac >> gvs[] >> NO_TAC)
  (* update_accounts (transfer_value ... o increment_nonce address) — ignore_bind *)
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  (* push_context *)
  >> strip_tac
  >> drule push_context_effect >> strip_tac >> gvs[]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> qexists`h0` >> simp[]
  >> simp[initial_msg_params_def]
  >> simp[lookup_account_def]
  >> cheat
QED

Theorem inl_grow_structure_abort_create_exists[simp]:
  inl_grow_structure (abort_create_exists x)
Proof
  rw[abort_create_exists_def]
  >> rw[ignore_bind_def, inl_grow_structure_def]
  >> gvs[bind_def, AllCaseEqs()]
  >> gvs[update_accounts_def, increment_nonce_def, bind_def, AllCaseEqs()]
  >> gvs[return_def, push_stack_def, inc_pc_def, bind_def, AllCaseEqs()]
  >> gvs[ignore_bind_def, assert_def, get_current_context_def, AllCaseEqs(),
         return_def, fail_def, bind_def, set_current_context_def] >>
  Cases_on`s.contexts` >> gvs[]
QED

Theorem inl_grow_structure_step_create[simp]:
  inl_grow_structure (step_create two)
Proof
  simp[step_create_def]
  >> rpt((irule inl_grow_structure_bind >> simp[] >> gen_tac)
     ORELSE (irule inl_grow_structure_ignore_bind >> simp[]))
  >> irule inl_grow_structure_cond >> simp[]
  >> irule inl_grow_structure_cond >> simp[]
QED

Theorem step_create_inl_grow_structure:
  s.contexts ≠ [] ∧ outputTo_consistent s ∧
  step_create two s = (INL (), s1) ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ∃callee_ctx pushed_rb parent_ctx.
      s1.contexts = (callee_ctx, pushed_rb) ::
                    (parent_ctx, SND (HD s.contexts)) ::
                    TL s.contexts ∧
      parent_ctx.msgParams = (FST (HD s.contexts)).msgParams ∧
      (∀a. (lookup_account a pushed_rb.accounts).storage =
           (lookup_account a s.rollback.accounts).storage) ∧
      (∀a. (lookup_account a s1.rollback.accounts).storage =
           (lookup_account a s.rollback.accounts).storage) ∧
      toSet s.rollback.accesses.storageKeys ⊆
        toSet pushed_rb.accesses.storageKeys ∧
      toSet s.rollback.accesses.storageKeys ⊆
        toSet s1.rollback.accesses.storageKeys ∧
      (∀address.
        callee_ctx.msgParams.outputTo = Code address ⇒
        callee_ctx.msgParams.callee = address)
Proof
  strip_tac >>
  mp_tac inl_grow_structure_step_create >>
  rewrite_tac[inl_grow_structure_def, outputTo_consistent_ctx_def] >>
  disch_then drule >> simp[]
QED

Theorem step_push_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∃child_ctx pushed_rb modified_parent_ctx.
      s'.contexts = (child_ctx, pushed_rb) ::
                    (modified_parent_ctx, SND (HD s.contexts)) ::
                    TL s.contexts ∧
      modified_parent_ctx.msgParams = (FST (HD s.contexts)).msgParams ∧
      (∀a. (lookup_account a s'.rollback.accounts).storage =
           (lookup_account a s.rollback.accounts).storage) ∧
      (∀a. (lookup_account a pushed_rb.accounts).storage =
           (lookup_account a s.rollback.accounts).storage) ∧
      toSet s.rollback.accesses.storageKeys ⊆
        toSet s'.rollback.accesses.storageKeys ∧
      toSet s.rollback.accesses.storageKeys ⊆
        toSet pushed_rb.accesses.storageKeys ∧
      outputTo_consistent_ctx child_ctx
Proof
  cheat
  (* Unfold step = handle inner handle_step, where inner = get ctx;
     if code ≤ pc then step_inst Stop else
     case FLOOKUP pc of NONE => step_inst Invalid | SOME op =>
     step_inst op; inc_pc_or_jump op.

     Split on whether inner returns INL or INR.

     Case A (inner INL ⇒ s' = inner's output):
       Stop/Invalid are preserves_same_frame, can't grow — vacuous.
       SOME op: step_inst op s = (INL _, s_mid); inc_pc_or_jump op
       is preserves_same_frame so s_mid and s' have same length.
       By step_inst_inl_grew_is_call, is_call op. For is_call op,
       inc_pc_or_jump op = return (), so s_mid = s'.
       Dispatch on op: Call-family uses step_call_inl_grow_structure,
       Create-family uses step_create_inl_grow_structure.

     Case B (inner INR ⇒ handle_step e r' = (_, s')):
       handle_step never grows (reraise preserves, handle_exception
       only pops). Combined with inner growing by at most 1 and
       LENGTH s' > LENGTH s, force LENGTH r' = LENGTH s + 1, LENGTH s'
       = LENGTH s + 1, i.e. handle_step preserved length exactly.
       handle_exception on LENGTH r' ≥ 2 always pops → contradiction
       unless we took the reraise branch, which requires vfm_abort e.
       So s' = r' (reraise). By step_inst_inr_grew_is_call_family +
       step_create_inr_no_grow, op is Call-family. Apply
       step_call_inr_grow_structure to get the structure; lift witnesses
       through same_frame_rel s sp.

     For the outputTo_consistent_ctx child conclusion: Call-family ops
     have outputTo = Memory _ (vacuously consistent); Create-family
     ops have outputTo = Code a with callee = a. *)
QED

(* -------------------------------------------------------------------------
 * Pop-structure lemma for step (Case −1 of run_call_inv_step).
 *
 * When step shrinks by 1 (pop), the resulting contexts structure is
 * derived from s.contexts by dropping the head and possibly modifying the
 * new head's context fields (msgParams preserved). The new rollback is
 * either s.rollback (success pop) or SND (HD s.contexts) (failure pop).
 * In both cases, this rollback is already tracked by run_call_inv's
 * invariant on active_rollbacks.
 * ------------------------------------------------------------------------- *)
(* Weakened from literal rollback equality to storage-pointwise
   disjunction, because handle_create in the Code+NONE+success case
   modifies rollback.accounts.code (but not .storage).

   The conclusion pairs each storage disjunct with the matching accesses
   subset:
     - Reraise-like pop (disjunct A): s.rollback.accesses ⊆ s'.rollback.accesses.
     - Failure pop (disjunct B): callee_rb.accesses ⊆ s'.rollback.accesses.
   (A single universal `s.accesses ⊆ s'.accesses` would fail in disjunct B.) *)
Theorem same_frame_or_grow_length:
  ∀m s r s'. same_frame_or_grow m ∧ m s = (r,s') ∧ s.contexts ≠ [] ⇒
    LENGTH s'.contexts ≥ LENGTH s.contexts
Proof
  rw[same_frame_or_grow_def]
  >> res_tac
  >> fs[same_frame_rel_def]
  >> decide_tac
QED

Theorem same_frame_or_grow_eq_length:
  ∀m s r s'. same_frame_or_grow m ∧ m s = (r,s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts = LENGTH s.contexts ⇒ same_frame_rel s s'
Proof
  rw[same_frame_or_grow_def] >> res_tac >> fs[same_frame_rel_def] >> decide_tac
QED

Theorem step_pop_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧
    LENGTH s'.contexts < LENGTH s.contexts ⇒
    ∃new_head parent rest.
      s.contexts = HD s.contexts :: parent :: rest ∧
      s'.contexts = (new_head, SND parent) :: rest ∧
      new_head.msgParams = (FST parent).msgParams ∧
      ((toSet s.rollback.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a s.rollback.accounts).storage)) ∨
       (toSet (SND (HD s.contexts)).accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a (SND (HD s.contexts)).accounts).storage)))
Proof
  rpt strip_tac
  >> qpat_x_assum `step s = (r,s')` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `inner s`
  >> Cases_on `inner s` >> Cases_on `q` >> gvs[Abbr `inner`]
  >- (rpt strip_tac >> assume_tac same_frame_or_grow_step_inner
      >> drule_all same_frame_or_grow_length >> fs[])
  >> rpt strip_tac
  >> ASSUME_TAC same_frame_or_grow_step_inner
  >> `LENGTH r'.contexts ≥ LENGTH s.contexts`
       by (drule_all same_frame_or_grow_length >> fs[])
  >> `r'.contexts ≠ []` by (Cases_on `r'.contexts` >> fs[])
  >> `LENGTH s'.contexts + 1 ≥ LENGTH r'.contexts ∧ LENGTH s'.contexts ≤ LENGTH r'.contexts`
       by (drule handle_step_shrinks_by_one >> fs[])
  >> `LENGTH r'.contexts = LENGTH s.contexts` by decide_tac
  >> `same_frame_rel s r'` by (drule_all same_frame_or_grow_eq_length >> fs[])
  >> `LENGTH s.contexts ≥ 2` by (
       CCONTR_TAC >> fs[]
       >> `LENGTH s.contexts ≤ 1` by decide_tac
       >> `LENGTH s.contexts = 1` by decide_tac
       >> drule handle_step_preserves_length_1 >> fs[])
  >> `s.contexts = HD s.contexts :: TL s.contexts`
       by (Cases_on `s.contexts` >> fs[])
  >> `LENGTH (TL s.contexts) ≥ 1`
       by (Cases_on `TL s.contexts` >> fs[])
  >> `?parent rest. TL s.contexts = parent :: rest`
       by (Cases_on `TL s.contexts` >> fs[])
  >> `r'.contexts ≠ []` by fs[same_frame_rel_def]
  >> `TL r'.contexts = TL s.contexts ∧ SND (HD r'.contexts) = SND (HD s.contexts)`
       by fs[same_frame_rel_def]
  >> `r'.contexts = (FST (HD r'.contexts), SND (HD s.contexts)) :: parent :: rest`
       by (Cases_on `r'.contexts` >> fs[] >> Cases_on `h` >> fs[])
  >> `LENGTH s'.contexts < LENGTH r'.contexts`
       by decide_tac
  >> drule_all handle_step_pop_generic_gen_paired
  >> disch_then (qx_choosel_then [`new_head`] assume_tac)
  >> qexistsl [`new_head`, `parent`, `rest`] >> simp[]
  >> disj2_tac
  >> conj_tac
  >- (match_mp_tac SUBSET_TRANS
      >> qexistsl [`toSet (SND (HD r'.contexts)).accesses.storageKeys`]
      >> simp[])
  >> rpt strip_tac
  >> first_x_assum (qspec_then `a` mp_tac)
  >> simp[]
QED

(* -------------------------------------------------------------------------
 * Single-step preservation of run_call_inv.
 *
 * Strategy: case on the length change. In each case, characterise
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
    (* active_rollbacks: tail unchanged. Using same_frame_rel's
       TL s1 = TL s0 and SND HD s1 = SND HD s0, so MAP SND of any
       TAKE prefix is the same. *)
    >> `∀n. MAP SND (TAKE n s1.contexts) = MAP SND (TAKE n s0.contexts)`
        by (
          `∃hd0 hd1 t. s0.contexts = hd0 :: t ∧ s1.contexts = hd1 :: t ∧
                       SND hd0 = SND hd1`
            by (Cases_on `s0.contexts` >> Cases_on `s1.contexts`
                >> gvs[] >> metis_tac[])
          >> simp[]
          >> Cases >> simp[])
    >> `active_rollbacks (LENGTH es.contexts) s1 =
          s1.rollback :: TL (active_rollbacks (LENGTH es.contexts) s0)`
        by (simp[active_rollbacks_def]
            >> `¬(LENGTH s0.contexts < LENGTH es.contexts)` by simp[]
            >> simp[])
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
    drule_all step_push_structure
    >> strip_tac
    >> qmatch_asmsub_rename_tac
        `s1.contexts = (child_ctx, pushed_rb) ::
                       (modified_parent_ctx, SND (HD s0.contexts)) ::
                       TL s0.contexts`
    (* outputTo_consistent_stack s1: new child + modified parent (same msgParams
       as old HD, which was consistent) + rest of old stack. *)
    >> `s1.contexts ≠ []` by simp[]
    >> `outputTo_consistent_stack s1` by (
         simp[outputTo_consistent_stack_def]
         >> fs[outputTo_consistent_stack_def]
         >> Cases_on `s0.contexts` >> fs[]
         >> PairCases_on `h` >> fs[]
         >> fs[outputTo_consistent_ctx_def])
    >> simp[]
    (* active_rollbacks ed s1 = s1.rollback :: pushed_rb :: MAP SND (TAKE ntk s0.contexts).
       Computed from active_rollbacks_def: TAKE m s1.contexts for m = LENGTH s1 - ed + 2. *)
    >> qabbrev_tac `ntk = LENGTH s0.contexts - LENGTH es.contexts + 2`
    >> `¬(LENGTH s0.contexts < LENGTH es.contexts) ∧
        ¬(LENGTH s1.contexts < LENGTH es.contexts)` by simp[]
    >> `LENGTH s1.contexts = LENGTH s0.contexts + 1` by (
       gvs[] >> Cases_on`s0.contexts` >> gvs[])
    >> `MAP SND s1.contexts = pushed_rb :: MAP SND s0.contexts` by (
         qpat_x_assum `s1.contexts = _` SUBST1_TAC
         >> Cases_on `s0.contexts` >> fs[])
    >> `active_rollbacks (LENGTH es.contexts) s1 =
          s1.rollback :: pushed_rb :: MAP SND (TAKE ntk s0.contexts)` by (
         simp[active_rollbacks_def, Abbr`ntk`, arithmeticTheory.ADD1]
         >> Cases_on `s0.contexts` >> gvs[])
    >> `active_rollbacks (LENGTH es.contexts) s0 =
          s0.rollback :: MAP SND (TAKE ntk s0.contexts)`
        by simp[active_rollbacks_def, Abbr`ntk`]
    >> simp[]
    (* Tail invariant transfers. *)
    >> `EVERY (λrb. storage_slot_preserved rb es.rollback)
              (MAP SND (TAKE ntk s0.contexts))`
        by (`EVERY (λrb. storage_slot_preserved rb es.rollback)
                   (active_rollbacks (LENGTH es.contexts) s0)`
              by fs[run_call_inv_def]
            >> rfs[])
    >> simp[]
    (* Head: storage_slot_preserved s1.rollback es.rollback. *)
    >> `storage_slot_preserved s0.rollback es.rollback`
        by (fs[run_call_inv_def, active_rollbacks_def])
    >> `storage_slot_preserved s1.rollback es.rollback ∧
        storage_slot_preserved pushed_rb es.rollback` suffices_by simp[]
    >> conj_tac
    >- (
      simp[storage_slot_preserved_def]
      >> rpt strip_tac
      >> `¬fIN (SK a k) s0.rollback.accesses.storageKeys`
          by (fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
              >> metis_tac[])
      >> `lookup_storage k (lookup_account a s0.rollback.accounts).storage =
          lookup_storage k (lookup_account a es.rollback.accounts).storage`
          by fs[storage_slot_preserved_def]
      >> metis_tac[])
    (* pushed_rb: its storage = s0's storage, and s0's accesses ⊆ its. *)
    >> simp[storage_slot_preserved_def]
    >> rpt strip_tac
    >> `¬fIN (SK a k) s0.rollback.accesses.storageKeys`
        by (fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
            >> metis_tac[])
    >> `lookup_storage k (lookup_account a s0.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage`
        by fs[storage_slot_preserved_def]
    >> metis_tac[])
  >> (
    (* CASE −1: pop. *)
    `LENGTH s1.contexts < LENGTH s0.contexts` by decide_tac
    >> drule_all step_pop_structure
    >> disch_then $ qx_choosel_then[`new_head`,`parent`,`rest`]assume_tac
    >> qmatch_asmsub_abbrev_tac `s0.contexts = callee_ctx :: parent :: rest`
    (* outputTo_consistent_stack s1: new_head has parent's msgParams. *)
    >> `outputTo_consistent_stack s1` by (
         `EVERY outputTo_consistent_ctx (MAP FST s0.contexts) ∧
          s0.contexts ≠ []`
           by fs[outputTo_consistent_stack_def]
         >> gvs[]
         >> simp[outputTo_consistent_stack_def,
                 outputTo_consistent_ctx_def]
         >> gvs[outputTo_consistent_ctx_def])
    >> simp[]
    (* active_rollbacks ed s1 vs active_rollbacks ed s0.
       LENGTH s1 = LENGTH s0 - 1. s1.contexts = (new_head, SND parent) :: rest.
       s0.contexts = HD :: parent :: rest. *)
    >> qabbrev_tac `ed = LENGTH es.contexts`
    >> `EVERY (λrb. storage_slot_preserved rb es.rollback)
              (active_rollbacks ed s0)`
         by fs[run_call_inv_def]
    >> `LENGTH s0.contexts = 2 + LENGTH rest ∧
        LENGTH s1.contexts = 1 + LENGTH rest`
        by (gvs[])
    >> `¬(LENGTH s0.contexts < ed)` by simp[]
    (* Key: show storage_slot_preserved s1.rollback es.rollback from the
       storage-pointwise disjunction + access monotonicity + the relevant
       s0-side slot-preserved facts. *)
    >> `storage_slot_preserved s0.rollback es.rollback ∧
        storage_slot_preserved (SND callee_ctx) es.rollback`
         by (qpat_x_assum `EVERY _ (active_rollbacks ed s0)` mp_tac
             >> simp[active_rollbacks_def]
             >> qpat_x_assum `s0.contexts = _` SUBST1_TAC
             >> `LENGTH s0.contexts + 2 - ed ≥ 2` by simp[]
             >> `∃n. LENGTH s0.contexts + 2 - ed = SUC (SUC n)` by
                  (Cases_on `LENGTH s0.contexts + 2 - ed` >> fs[]
                   >> Cases_on `n` >> fs[])
             >> simp[] >> strip_tac >> fs[])
    >> `storage_slot_preserved s1.rollback es.rollback` by (
         (* step_pop_structure's conclusion is a disjunction of
            (accesses-subset ∧ storage-eq) pairs. Case-split and discharge
            each via the matching subset and the corresponding
            storage_slot_preserved hypothesis. *)
         simp[storage_slot_preserved_def]
         >> rpt strip_tac
         >> gvs[]
         >- (
           (* Disjunct A: s.accesses ⊆ s'.accesses ∧ storage s' = storage s. *)
           `¬fIN (SK a k) s0.rollback.accesses.storageKeys`
             by (fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
                 >> metis_tac[])
           >> `lookup_storage k (lookup_account a s0.rollback.accounts).storage =
               lookup_storage k (lookup_account a es.rollback.accounts).storage`
                by fs[storage_slot_preserved_def]
           >> fs[lookup_storage_def]
           >> metis_tac[])
         >>
           (* Disjunct B: callee_rb.accesses ⊆ s'.accesses ∧
              storage s' = storage callee_rb. *)
           `¬fIN (SK a k) (SND callee_ctx).accesses.storageKeys`
             by (gvs[]
                 >> gvs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
                 >> metis_tac[])
           >> `lookup_storage k (lookup_account a (SND callee_ctx).accounts).storage =
               lookup_storage k (lookup_account a es.rollback.accounts).storage`
                by fs[storage_slot_preserved_def])
    (* Split on whether s1.contexts is below ed or not. *)
    >> Cases_on `LENGTH s1.contexts < ed`
    >- ((* LENGTH s1 < ed: active_rollbacks s1 = [s1.rollback]. *)
        simp[active_rollbacks_def])
    (* LENGTH s1 ≥ ed. Both active_rollbacks have a non-trivial tail.
       s0's TAKE takes one more element than s1's. *)
    >> qpat_x_assum `EVERY _ (active_rollbacks ed s0)` mp_tac
    >> simp[active_rollbacks_def]
QED

(* -------------------------------------------------------------------------
 * Main run_call preservation theorem.
 * ------------------------------------------------------------------------- *)

Theorem run_call_preserves_inv:
  ∀es res es'.
    outputTo_consistent_stack es ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
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
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
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
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
    run_call es = SOME (r, es') ⇒
    es'.txParams = es.txParams
Proof
  rpt strip_tac
  >> drule_all run_call_preserves_inv
  >> rw[run_call_inv_def]
QED
