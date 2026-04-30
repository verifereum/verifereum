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
  vfmStoragePredicates vfmSameFrame vfmStaticCalls
  vfmDecreasesGas vfmStepLength vfmHandleStep vfmRunWithinFrame
  vfmJumpDest
Libs
  dep_rewrite BasicProvers

(* -------------------------------------------------------------------------
 * Active rollbacks — the list of rollbacks we could "revert to" from a
 * descendant state s of es. The current s.rollback plus the saved
 * rollbacks of every context pushed from es-depth onward (inclusive
 * of the context at es-depth itself, so that a failure-pop at
 * exactly es-depth restores a tracked rollback).
 *
 * The TAKE excludes the LAST context's saved rollback: it can never be
 * restored as s.rollback during run_call (at depth 1, handle_exception
 * sees n ≤ 1 and does not pop), yet set_original in proceed_create
 * modifies it by replacing the CREATE target's account with
 * empty_account_state, potentially breaking storage_slot_preserved.
 * The MIN ensures we take enough for pop-restore tracking while never
 * including the LAST position.
 * ------------------------------------------------------------------------- *)

Definition active_rollbacks_def:
  active_rollbacks es_depth s =
    s.rollback ::
    (if LENGTH s.contexts < es_depth then []
     else MAP SND (TAKE (MIN (LENGTH s.contexts - es_depth + 1)
                              (LENGTH s.contexts - 1)) s.contexts))
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
    wf_state s ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (active_rollbacks (LENGTH es.contexts) s)
End

(* -------------------------------------------------------------------------
 * Reflexivity.
 * ------------------------------------------------------------------------- *)

Theorem run_call_inv_refl:
  outputTo_consistent_stack es ∧ wf_state es ∧
  (FST (HD es.contexts)).jumpDest = NONE ∧
  EVERY (λrb. storage_slot_preserved rb es.rollback)
        (MAP SND (TAKE 2 es.contexts)) ⇒
  run_call_inv es es
Proof
  rw[run_call_inv_def, active_rollbacks_def, storage_slot_preserved_def]
  >> gvs[outputTo_consistent_stack_def]
  >> Cases_on `es.contexts` >> gvs[]
  >> rw[MIN_DEF]
  >> Cases_on`t` >> gvs[ADD1]
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

(* proceed_call_push_structure: combined structural lemma for proceed_call.
   When proceed_call pushes a new frame:
   - TL is preserved (old contexts unchanged)
   - Accesses are monotone
   - The new context's outputTo equals the parameter outputTo
   Note: outputTo_consistent follows at step_call level since outputTo = Memory ... *)
Theorem proceed_call_push_structure:
  proceed_call op sender address value argsOffset argsSize code stipend
               outputTo s = (r, s') ∧ s.contexts ≠ [] ⇒
  TL s'.contexts = s.contexts ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  (FST (HD s'.contexts)).msgParams.outputTo = outputTo ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def]
  >> simp[bind_def, get_rollback_def, return_def]
  >> simp[read_memory_def, bind_def, return_def, get_current_context_def]
  >> qmatch_goalsub_abbrev_tac `ignore_bind g`
  >> simp[ignore_bind_def, Once bind_def]
  >> TOP_CASE_TAC
  >> qmatch_asmsub_rename_tac `g s = (q, s1)`
  (* g is either update_accounts (transfer_value ...) or return () —
     both preserve contexts and accesses *)
  >> `s1.contexts = s.contexts ∧
      toSet s.rollback.accesses.storageKeys ⊆ toSet s1.rollback.accesses.storageKeys`
      by (simp[Abbr`g`] >> gvs[COND_RATOR,AllCaseEqs(),update_accounts_def, return_def])
  >> `ISL q` by (gvs[Abbr`g`,AllCaseEqs(),COND_RATOR,return_def,
                     update_accounts_def])
  >> TOP_CASE_TAC >> gvs[]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
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
  (* After push_context: TL = s1.contexts = s.contexts *)
  >> qmatch_asmsub_abbrev_tac `push_context (ctx, _) s1`
  >> reverse IF_CASES_TAC >> simp[return_def]
  >- ((* No precompile *)
      strip_tac >> gvs[Abbr`ctx`, initial_msg_params_def] >>
      gvs[SUBSET_DEF] )
  (* Precompile: dispatch_precompiles is preserves_same_frame *)
  >> strip_tac
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles addr ss = (_, s')`
  >> `ss.contexts ≠ []` by simp[Abbr`ss`]
  >> qmatch_asmsub_abbrev_tac`dpa ss = (_,_)`
  >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
  >> pop_assum mp_tac
  >> rewrite_tac[preserves_same_frame_def]
  >> disch_then drule
  >> `ss.contexts = (ctx, s.rollback) :: s.contexts` by simp[Abbr`ss`]
  >> simp[same_frame_rel_def]
  >> strip_tac >> gvs[SUBSET_DEF]
  >> gvs[Abbr`ctx`,initial_context_def, initial_msg_params_def]
  >> gvs[Abbr`ss`]
QED

(* proceed_create_push_structure: combined structural lemma for proceed_create.
   When proceed_create pushes a new frame:
   - FST parts of TL are preserved (SND parts may change due to ensure_storage_in_domain)
   - Accesses are monotone
   - The new head context is outputTo_consistent (outputTo = Code address
     and callee = address) *)
Theorem proceed_create_push_structure:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ⇒
  MAP FST (TL s'.contexts) = MAP FST s.contexts ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def]
  (* update_accounts (increment_nonce senderAddress) *)
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  (* get_rollback *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  (* get_original / set_original: don't modify contexts or accesses *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  (* update_accounts (transfer_value o increment_nonce) *)
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  (* push_context *)
  >> strip_tac
  >> drule push_context_effect >> strip_tac >> gvs[]
  (* outputTo_consistent: outputTo = Code address, callee = address *)
  >> simp[outputTo_consistent_ctx_def, initial_context_def,
          initial_msg_params_def]
  >> simp[set_last_accounts_def, MAP_SNOC, MAP_FRONT]
  >> qspec_then`MAP FST s.contexts`mp_tac SNOC_LAST_FRONT
  >> simp[]
  (* SND (HD s'.contexts) = captured rollback = s.rollback (after increment_nonce,
     which doesn't modify accesses), so accesses subset is reflexivity *)
  >> gvs[SUBSET_DEF]
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

(* step_call_push_structure: when step_call grows, structural facts.
   We peel prefix ops one by one using bind_psf_grows_extract, which gives
   us same_frame_rel at each step. Composing transitively gives same_frame_rel s sm
   where sm is the state just before proceed_call. Then proceed_call_push_structure
   gives us TL s'.contexts = sm.contexts, from which we derive all conclusions. *)
Theorem step_call_push_structure:
  step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  TL (TL s'.contexts) = TL s.contexts ∧
  SND (HD (TL s'.contexts)) = SND (HD s.contexts) ∧
  (FST (HD (TL s'.contexts))).msgParams = (FST (HD s.contexts)).msgParams ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  simp[step_call_def] >> strip_tac
  (* Peel pop_stack *)
  >> qmatch_asmsub_abbrev_tac`pop_stack n`
  >> `preserves_same_frame (pop_stack n)` by simp[]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> pairarg_tac >> gvs[]
  >> `sm.contexts ≠ []` by (strip_tac >> gvs[same_frame_rel_def])
  >> `LENGTH sm.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
  (* Peel memory_expansion_info *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ sm = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sm s2`
  >> `same_frame_rel s s2` by metis_tac[same_frame_rel_trans]
  >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel consume_gas *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s2 s3`
  >> `same_frame_rel s s3` by metis_tac[same_frame_rel_trans]
  >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel expand_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s3 s4`
  >> `same_frame_rel s s4` by metis_tac[same_frame_rel_trans]
  >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s4 s5`
  >> `same_frame_rel s s5` by metis_tac[same_frame_rel_trans]
  >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> pairarg_tac >> gvs[]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s5 s6`
  >> `same_frame_rel s s6` by metis_tac[same_frame_rel_trans]
  >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> pairarg_tac >> gvs[ignore_bind_def]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s6 s7`
  >> `same_frame_rel s s7` by metis_tac[same_frame_rel_trans]
  >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s7 s8`
  >> `same_frame_rel s s8` by metis_tac[same_frame_rel_trans]
  >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s8 s9`
  >> `same_frame_rel s s9` by metis_tac[same_frame_rel_trans]
  >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_callee *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s9 s0`
  >> `same_frame_rel s s0` by metis_tac[same_frame_rel_trans]
  >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> gvs[Ntimes COND_RATOR 2]
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
  >> Cases_on`bbb` >> gs[]
  >- (
    drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
    >> simp[])
  (* Peel set_return_data via ignore_bind *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s0 sa`
  >> `same_frame_rel s sa` by metis_tac[same_frame_rel_trans]
  >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_num_contexts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sa sb`
  >> `same_frame_rel s sb` by metis_tac[same_frame_rel_trans]
  >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Now at the conditional: if value check then abort else continue *)
  (* Second conditional: if depth/code check then abort else proceed_call *)
  >> gvs[COND_RATOR]
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
  >> Cases_on`bbb` >> gs[]
  >- (
    drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
    >> simp[])
  (* Now we have proceed_call sm = (_, s') with growth, and same_frame_rel s sm *)
  >> drule_all proceed_call_push_structure
  >> strip_tac
  (* From same_frame_rel s sm: sm.contexts = s.contexts *)
  >> `TL sb.contexts = TL s.contexts` by ( fs[same_frame_rel_def] )
  >> gvs[]
  >> conj_asm1_tac >- gvs[same_frame_rel_def]
  >> conj_asm1_tac >- gvs[same_frame_rel_def]
  >> conj_tac >- metis_tac[SUBSET_TRANS, same_frame_rel_def]
  (* outputTo_consistent: outputTo = Memory from step_call, so Code a is vacuous *)
  >> conj_tac >- simp[outputTo_consistent_ctx_def]
  >> metis_tac[SUBSET_TRANS, same_frame_rel_def]
QED

(* TODO: move *)
Theorem LAST_CONS_SNOC:
  LAST (x::(SNOC y z)) = y
Proof
  map_every qid_spec_tac[`x`,`y`,`z`] >> Induct >> rw[]
QED

(* TODO: move *)
Theorem FRONT_CONS_SNOC:
  FRONT (x::(SNOC y z)) = x::z
Proof
  map_every qid_spec_tac[`x`,`y`,`z`] >> Induct >> rw[] >>
  rewrite_tac[GSYM SNOC_APPEND] >> rw[]
QED

(* step_create_push_structure: structural facts when step_create grows.
   We peel prefix ops using bind_psf_grows_extract to get same_frame_rel s sm.
   proceed_create modifies LAST context's SND.accounts via set_original,
   so we only claim accesses preservation (not storage equality) for per-position
   SND facts. For the old head (position 1 in new stack), we additionally
   claim storage equality for a ≠ callee, since set_original only modifies
   the callee address. *)
Theorem step_create_push_structure:
  step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
  (∀i. i < LENGTH s.contexts ⇒
       (SND (EL i (TL s'.contexts))).accesses = (SND (EL i s.contexts)).accesses) ∧
  (FST (HD (TL s'.contexts))).msgParams = (FST (HD s.contexts)).msgParams ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys ∧
  (∀a. a ≠ (FST (HD s'.contexts)).msgParams.callee ⇒
     (lookup_account a (SND (HD (TL s'.contexts))).accounts).storage =
     (lookup_account a (SND (HD s.contexts)).accounts).storage) ∧
  (∀i. i < LENGTH s.contexts - 1 ⇒
     (SND (EL i (TL s'.contexts))).accounts =
     (SND (EL i s.contexts)).accounts) ∧
  (∀a. a ≠ (FST (HD s'.contexts)).msgParams.callee ⇒
    (lookup_account a (SND (EL (LENGTH s.contexts) s'.contexts)).accounts).storage =
    (lookup_account a (SND (LAST s.contexts)).accounts).storage)
Proof
  simp[step_create_def] >> strip_tac
  (* Peel pop_stack *)
  >> qmatch_asmsub_abbrev_tac`pop_stack n`
  >> `preserves_same_frame (pop_stack n)` by simp[]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> `sm.contexts ≠ []` by (strip_tac >> gvs[same_frame_rel_def])
  >> `LENGTH sm.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
  (* Peel memory_expansion_info *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ sm = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sm s2`
  >> `same_frame_rel s s2` by metis_tac[same_frame_rel_trans]
  >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel consume_gas *)
  >> gvs[ignore_bind_def]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s2 s3`
  >> `same_frame_rel s s3` by metis_tac[same_frame_rel_trans]
  >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel expand_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s3 s4`
  >> `same_frame_rel s s4` by metis_tac[same_frame_rel_trans]
  >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel read_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s4 s5`
  >> `same_frame_rel s s5` by metis_tac[same_frame_rel_trans]
  >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_callee *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s5 s6`
  >> `same_frame_rel s s6` by metis_tac[same_frame_rel_trans]
  >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_accounts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s6 s7`
  >> `same_frame_rel s s7` by metis_tac[same_frame_rel_trans]
  >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel assert (code length) via ignore_bind *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s7 s8`
  >> `same_frame_rel s s8` by metis_tac[same_frame_rel_trans]
  >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel access_address *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s8 s9`
  >> `same_frame_rel s s9` by metis_tac[same_frame_rel_trans]
  >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_gas_left *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s9 s0`
  >> `same_frame_rel s s0` by metis_tac[same_frame_rel_trans]
  >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel consume_gas (cappedGas) *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s0 sa`
  >> `same_frame_rel s sa` by metis_tac[same_frame_rel_trans]
  >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel assert_not_static *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sa sb`
  >> `same_frame_rel s sb` by metis_tac[same_frame_rel_trans]
  >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel set_return_data *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sb sc`
  >> `same_frame_rel s sc` by metis_tac[same_frame_rel_trans]
  >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_num_contexts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sc sd`
  >> `same_frame_rel s sd` by metis_tac[same_frame_rel_trans]
  >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel ensure_storage_in_domain *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sd se`
  >> `same_frame_rel s se` by metis_tac[same_frame_rel_trans]
  >> `se.contexts ≠ [] ∧ LENGTH se.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Now at the conditional *)
  >> gvs[Ntimes COND_RATOR 2]
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
  >> qpat_x_assum`COND bbb _ _ = _`mp_tac
  >> IF_CASES_TAC
  >- ((* abort_unuse: preserves_same_frame, can't grow *)
      strip_tac >>
      drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
      >> simp[])
  >> IF_CASES_TAC
  >- ((* abort_create_exists: length_preserves, can't grow *)
      strip_tac >>
      drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists)
      >> simp[])
  (* Now we have proceed_create sf = (_, s') with growth, and same_frame_rel s sf *)
  >> strip_tac
  >> drule_all proceed_create_push_structure
  >> strip_tac
  (* From same_frame_rel s sf: TL sf.contexts = TL s.contexts *)
  >> `TL se.contexts = TL s.contexts` by gvs[same_frame_rel_def]
  >> gvs[]
  >> conj_asm1_tac >- (
    qpat_x_assum`same_frame_rel s se`mp_tac >>
    simp[same_frame_rel_def] >> strip_tac >>
    Cases_on`s'.contexts` >> gvs[] >>
    Cases_on`t` >> gvs[] >>
    Cases_on`se.contexts` >> gvs[] )
  (* Remaining: per-pos accesses, msgParams, rollback, outputTo, SND(HD),
     a≠callee storage *)
  >> rewrite_tac[Ntimes CONJ_ASSOC 3]
  >> reverse conj_tac >- (
    (* a ≠ callee ⇒ storage equality at position 1.
       set_last_accounts only modifies the LAST element's .accounts.
       When LENGTH se.contexts > 1, HD of TL is NOT the last, so unchanged.
       When LENGTH se.contexts = 1, HD of TL IS the last, modified by
       set_last_accounts (update_account address empty_account_state)
       which doesn't touch a ≠ address. *)
    qpat_x_assum `proceed_create _ _ _ _ _ se = _` mp_tac >>
    rewrite_tac[proceed_create_def] >>
    simp[ignore_bind_def, bind_def, update_accounts_def, return_def,
          get_rollback_def, get_original_def, set_original_def, fail_def] >>
    strip_tac >> gvs[] >>
    drule push_context_effect >> strip_tac >> gvs[] >>
    simp[lookup_storage_def, lookup_account_def] >>
    qmatch_goalsub_abbrev_tac`SND (EL _ (slc uc _))` >>
    qmatch_goalsub_abbrev_tac`(SND (EL _ icc)).accounts _` >>
    gvs[push_context_def,return_def,execution_state_component_equality] >>
    gvs[account_already_created_def,lookup_account_def] >>
    Cases_on`s.contexts` >- gvs[] >> simp[] >>
    Cases_on`se.contexts` >- gvs[] >> simp[Abbr`slc`] >>
    gvs[set_last_accounts_def] >>
    simp[EL_SNOC] >>
    simp[Abbr`icc`] >>
    qmatch_goalsub_abbrev_tac`EL (LENGTH t) (SNOC sn fr)` >>
    `LENGTH fr = LENGTH t` by simp[Abbr`fr`] >>
    pop_assum(SUBST1_TAC o SYM) >> simp[EL_LENGTH_SNOC,Abbr`sn`] >>
    gvs[Abbr`fr`] >>
    `SND h = SND h'` by (
      qpat_x_assum`same_frame_rel s se`mp_tac >>
      simp[same_frame_rel_def] ) >>
    simp[initial_msg_params_def] >>
    reverse(qspec_then`t`FULL_STRUCT_CASES_TAC SNOC_CASES >> gvs[]) >- (
      simp[LAST_CONS_SNOC, FRONT_CONS_SNOC] >>
      conj_tac >- ( Cases >> simp[EL_SNOC] ) >>
      simp[Abbr`uc`, update_account_def, APPLY_UPDATE_THM] >>
      gen_tac >> simp[LAST_CONS_SNOC] ) >>
    simp[Abbr`uc`, lookup_account_def, update_account_def, APPLY_UPDATE_THM] )
  >> simp[GSYM CONJ_ASSOC]
  >> reverse conj_tac >- (
    (* SND (HD s'.contexts) accesses subset *)
    reverse conj_tac
    >- metis_tac[SUBSET_TRANS, same_frame_rel_def] >>
    (* msgParams *)
    qpat_x_assum`same_frame_rel s se`mp_tac >>
    simp[same_frame_rel_def] >> strip_tac >>
    Cases_on`s.contexts` >- gvs[] >> simp[] >>
    Cases_on`s'.contexts` >- gvs[] >> simp[] >>
    Cases_on`t'` >- gvs[] >> simp[] >>
    Cases_on`se.contexts` >- gvs[] >>
    fs[]  )
  (* Per-position accesses preservation: set_original only touches .accounts *)
  >> qpat_x_assum `proceed_create _ _ _ _ _ se = _` mp_tac
  >> simp[proceed_create_def]
  >> simp[ignore_bind_def, bind_def, update_accounts_def, return_def,
          get_rollback_def, get_original_def, set_original_def, fail_def]
  >> strip_tac >> gvs[]
  >> drule push_context_effect >> strip_tac >> gvs[]
  (* TL s'.contexts = set_last_accounts ... sf.contexts *)
  >> rpt strip_tac
  >> `i < LENGTH se.contexts` by gvs[same_frame_rel_def]
  >> simp[set_last_accounts_def]
  >> qmatch_goalsub_abbrev_tac`SNOC new`
  >> qhdtm_x_assum`push_context` kall_tac
  >> qpat_x_assum`_ = TL s.contexts`mp_tac
  >> simp[LIST_EQ_REWRITE] >> rewrite_tac[GSYM EL]
  >> Cases_on`i=0` >- (
    Cases_on`FRONT se.contexts = []`
    >- (
      gvs[] >>
      gvs[Abbr`new`] >>
      Cases_on`se.contexts` >> gvs[] >>
      Cases_on`s.contexts` >> gvs[] >>
      qpat_x_assum`same_frame_rel s se`mp_tac >>
      simp[same_frame_rel_def] ) >>
    rewrite_tac[GSYM EL] >>
    DEP_REWRITE_TAC[EL_SNOC] >>
    simp[LENGTH_FRONT] >>
    simp[PRE_SUB1] >>
    Cases_on`se.contexts` >> gvs[] >>
    Cases_on`s.contexts` >> gvs[] >>
    Cases_on`t` >> gvs[] >>
    qpat_x_assum`same_frame_rel s se`mp_tac >>
    simp[same_frame_rel_def] )
  >> Cases_on`i = LENGTH s.contexts - 1`
  >- (
    `i = LENGTH (FRONT se.contexts)` by simp[LENGTH_FRONT] >>
    pop_assum SUBST1_TAC >>
    simp[EL_LENGTH_SNOC] >>
    simp[Abbr`new`, LENGTH_FRONT, GSYM LAST_EL] >>
    simp[LAST_EL] >> strip_tac >>
    AP_TERM_TAC >> AP_TERM_TAC >>
    first_x_assum(qspec_then`PRE i`mp_tac) >>
    simp[PRE_SUB1,ADD1] )
  >> strip_tac
  >> simp[EL_SNOC, LENGTH_FRONT, EL_FRONT, NULL_EQ]
  >> first_x_assum(qspec_then`PRE i`mp_tac)
  >> simp[ADD1, PRE_SUB1]
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

Theorem same_frame_or_grow_length:
  ∀m s r s'. same_frame_or_grow m ∧ m s = (r,s') ∧ s.contexts ≠ [] ⇒
    LENGTH s'.contexts ≥ LENGTH s.contexts
Proof
  rw[same_frame_or_grow_def]
  >> res_tac
  >> fs[same_frame_rel_def]
  >> decide_tac
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
Theorem step_push_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧ wf_state s ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH s'.contexts = LENGTH s.contexts + 1 ∧
    (* Storage preservation for s'.rollback *)
    (∀a. (lookup_account a s'.rollback.accounts).storage =
         (lookup_account a s.rollback.accounts).storage) ∧
    toSet s.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys ∧
    (* Per-position storage facts for saved rollbacks in s'.contexts *)
    (* Per-position storage: excludes i = LENGTH s.contexts (the old LAST
       position) because set_original in proceed_create replaces the
       callee account with empty_account_state, breaking ∀a storage
       equality at that position for the CREATE case. The accesses-subset
       clause still covers all positions since set_original only touches
       .accounts, not .accesses. *)
    (∀i. i < LENGTH s.contexts ⇒
         (∀a. (lookup_account a (SND (EL i s'.contexts)).accounts).storage =
              (lookup_account a (if i = 0 then s.rollback
                                 else SND (EL (i-1) s.contexts)).accounts).storage)) ∧
    (∀i. i < LENGTH s'.contexts ⇒
         toSet (if i = 0 then s.rollback
                else SND (EL (i-1) s.contexts)).accesses.storageKeys ⊆
           toSet (SND (EL i s'.contexts)).accesses.storageKeys) ∧
    (* msgParams preservation at position 1 *)
    (LENGTH s.contexts ≥ 1 ⇒
       (FST (EL 1 s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams) ∧
    (* outputTo_consistent for the new child *)
    outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
    (* outputTo_consistent preserved for rest of stack *)
    (∀i. i < LENGTH s.contexts ⇒
         outputTo_consistent_ctx (FST (EL i s.contexts)) ⇒
         outputTo_consistent_ctx (FST (EL (i+1) s'.contexts)))
Proof
  rpt gen_tac >> strip_tac
  (* Unfold step = handle inner handle_step *)
  >> qpat_x_assum `step s = _` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `inner s`
  >> Cases_on `inner s` >> Cases_on `q`
  (* Case: inner returned INL - step returns inner's result *)
  >- (
    simp[] >> strip_tac >> gvs[]
    (* inner = get_ctx; step_inst; inc_pc_or_jump *)
    >> gvs[Abbr`inner`, bind_def,AllCaseEqs()]
    >> gvs[get_current_context_def, return_def, fail_def, bind_def]
    >> gvs[COND_RATOR, CaseEq"bool"]
    (* Case: code ≤ pc, step_inst Stop *)
    >- (
      `preserves_same_frame (step_inst Stop)` by simp[]
      >> drule_all psf_imp_length_contexts_preserved
      >> simp[])
    (* Case: FLOOKUP *)
    >> gvs[option_CASE_rator,CaseEq"option"]
    (* NONE: step_inst Invalid *)
    >- (
      `preserves_same_frame (step_inst Invalid)` by simp[]
      >> drule_all psf_imp_length_contexts_preserved
      >> simp[])
    (* SOME op: step_inst op; inc_pc_or_jump op *)
    >> gvs[ignore_bind_def, bind_def]
    >> gvs[AllCaseEqs()]
    >> rename1 `step_inst op s0 = (INL (), s1)`
    >> drule_at Any psf_imp_length_contexts_preserved
    >> simp[]
    >> impl_keep_tac >- (strip_tac >>
         gvs[inc_pc_or_jump_def,COND_RATOR,AllCaseEqs(),return_def] >>
         gvs[bind_def,get_current_context_def,fail_def,AllCaseEqs()] )
    >> strip_tac
    >> `LENGTH s1.contexts > LENGTH s0.contexts` by simp[]
    (* By step_inst_inl_grew_is_call, is_call op *)
    >> `is_call op` by metis_tac[step_inst_inl_grew_is_call]
    (* For is_call, inc_pc_or_jump = return (), so s' = s1 *)
    >> `r' = s1` by (
         gvs[inc_pc_or_jump_def, return_def, COND_RATOR, CaseEq"bool"])
    >> gvs[]
    >> `outputTo_consistent s0` by (
         gvs[outputTo_consistent_def, outputTo_consistent_stack_def]
         >> Cases_on`s0.contexts`
         >> gvs[outputTo_consistent_ctx_def])
    (* Case split on which call/create op *)
    >> Cases_on `∃two. step_inst op s0 = step_create two s0`
    >- (
      (* CREATE/CREATE2 case *)
      gvs[] >> pop_assum(assume_tac o SYM) >>
      (* Use step_create lemmas *)
      drule_then drule step_create_grows_by_exactly_one
      >> simp[] >> strip_tac
      (* s1.rollback storage preserved *)
      >> `preserves_storage (step_create two)` by simp[preserves_storage_step_create]
      >> gvs[preserves_storage_def]
      >> pop_assum drule >> strip_tac
      >> gvs[lookup_storage_def, FUN_EQ_THM]
      (* Use step_create_push_structure *)
      >> drule step_create_push_structure
      >> simp[]
      >> strip_tac
      >> drule_then drule step_create_pushed_rb_storage
      >> simp[] >> strip_tac
      >> conj_tac
      >- ( Cases >> simp[] >> Cases_on`r'.contexts` >> gvs[] )
      >> conj_tac >- ( Cases >> gvs[] >> Cases_on`r'.contexts` >> gvs[] )
      >> conj_tac
      >- ( Cases_on`s0.contexts` >> gvs[] >> Cases_on`r'.contexts` >> gvs[] )
      >> Cases_on`s0.contexts` >> gvs[]
      >> Cases_on`r'.contexts` >> gvs[]
      >> Cases_on`t'` >> gvs[]
      >> Cases >> gvs[EL_CONS]
      >- ( simp[outputTo_consistent_ctx_def] )
      >> gvs[PRE_SUB1,ADD1]
      >> simp[outputTo_consistent_ctx_def]
      >> gvs[LIST_EQ_REWRITE,EL_MAP])
    >> (
      (* CALL family case *)
      `step_inst op s0 = step_call op s0`
      by (Cases_on`op` >> gvs[step_inst_def, is_call_def])
      (* Use step_call lemmas *)
      >> gvs[]
      >> drule_then drule step_call_grows_by_exactly_one
      >> simp[] >> strip_tac
      (* s1.rollback storage preserved *)
      >> drule(REWRITE_RULE[preserves_storage_def]preserves_storage_step_call)
      >> simp[lookup_storage_def, FUN_EQ_THM]
      >> strip_tac
      >> drule_all step_call_pushed_rb_storage
      >> strip_tac
      (* Use step_call_push_structure *)
      >> drule_all step_call_push_structure
      >> strip_tac
      >> simp[]
      >> conj_tac
      >- (
        Cases >> gvs[ADD1] >>
        Cases_on`r'.contexts` >> gvs[EL_CONS,PRE_SUB1] >>
        Cases_on`s0.contexts` >> gvs[ADD1] >>
        Cases_on`t` >> gvs[ADD1] >>
        Cases_on`n` >> gvs[ADD1] )
      >> Cases_on`r'.contexts` >> gvs[EL_CONS, PRE_SUB1]
      >> Cases_on`t` >> gvs[EL_CONS, PRE_SUB1, ADD1]
      >> Cases_on`s0.contexts` >> gvs[EL_CONS, PRE_SUB1, ADD1]
      >> conj_tac >> Cases >> gvs[ADD1]
      >- ( Cases_on`n` >> gvs[] )
      >> gvs[outputTo_consistent_ctx_def]))
  (* Case: inner returned INR - handle_step runs *)
  >> simp[]
  >> rename1 `handle_step e r' = (_, s')`
  (* inner is same_frame_or_grow *)
  >> `same_frame_or_grow inner` by simp[Abbr`inner`]
  >> `LENGTH r'.contexts ≥ LENGTH s.contexts` by (
       drule_all same_frame_or_grow_length >> simp[])
  >> strip_tac
  >> `r'.contexts ≠ []` by (strip_tac >> gvs[] >> Cases_on`s.contexts` >> gvs[])
  (* For LENGTH s' > LENGTH s with inner INR, we derive a contradiction.
     The inner INR-grew, so by step_inner_inr_grow_not_abort, ¬vfm_abort e.
     With ¬vfm_abort e and LENGTH r' ≥ 2, handle_step_not_abort_pops says
     handle_step shrinks by exactly 1: LENGTH s' + 1 = LENGTH r'.
     By step_inner_grows_by_exactly_one, LENGTH r' = LENGTH s + 1.
     So LENGTH s' + 1 = LENGTH s + 1, giving LENGTH s' = LENGTH s.
     This contradicts LENGTH s' > LENGTH s. *)
  >> `LENGTH s'.contexts ≤ LENGTH s.contexts` suffices_by gvs[]
  >> Cases_on `LENGTH r'.contexts = LENGTH s.contexts` >- (
       drule handle_step_shrinks_by_one >> simp[])
  (* inner grew *)
  >> `LENGTH r'.contexts > LENGTH s.contexts` by simp[]
  >> `outputTo_consistent s` by
       metis_tac[outputTo_consistent_stack_imp_consistent]
  >> `¬vfm_abort e` by (
       irule step_inner_inr_grow_not_abort
       >> qexistsl_tac [`s`, `r'`] >> simp[Abbr`inner`])
  >> `0 < LENGTH s.contexts` by (Cases_on`s.contexts` >> gvs[])
  >> `LENGTH r'.contexts ≥ 2` by simp[]
  (* Inner grew by exactly 1 *)
  >> `LENGTH r'.contexts = LENGTH s.contexts + 1` by (
       qunabbrev_tac`inner` >>
       drule_then drule step_inner_grows_by_exactly_one >> gvs[])
  (* Need EVERY (wf_context o FST) r'.contexts to apply handle_step_not_abort_pops *)
  >> drule_at(Pat`handle_step`) handle_step_not_abort_pops
  >> gvs[]
  >> `decreases_gas_cred T 0 0 inner` suffices_by (
    gvs[decreases_gas_cred_def] >>
    disch_then(qspec_then`s`mp_tac) >> rw[] >>
    gvs[wf_state_def] >>
    gvs[EVERY_MEM] ) >>
  simp[Abbr`inner`] >>
  irule decreases_gas_cred_bind_mono >>
  qexistsl_tac[`T`,`F`] >> simp[] >> gen_tac >>
  rw[] >> CASE_TAC >> rw[] >>
  irule decreases_gas_cred_ignore_bind_mono >> rw[] >>
  qexistsl_tac[`F`,`T`] >> simp[]
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
  >> `LENGTH r'.contexts >= LENGTH s.contexts`
       by (drule_all same_frame_or_grow_length >> fs[])
  >> `r'.contexts <> []` by (Cases_on `r'.contexts` >> fs[])
  >> `LENGTH s'.contexts + 1 >= LENGTH r'.contexts /\ LENGTH s'.contexts <= LENGTH r'.contexts`
       by (drule handle_step_shrinks_by_one >> fs[])
  >> `LENGTH r'.contexts = LENGTH s.contexts` by decide_tac
  >> `same_frame_rel s r'` by (drule_all same_frame_or_grow_eq_length >> fs[])
  >> `LENGTH s.contexts >= 2` by (
       CCONTR_TAC >> fs[]
       >> `LENGTH s.contexts <= 1` by decide_tac
       >> `LENGTH s.contexts = 1` by decide_tac
       >> drule handle_step_preserves_length_1 >> fs[])
  >> `s.contexts = HD s.contexts :: TL s.contexts`
       by (Cases_on `s.contexts` >> fs[])
  >> `LENGTH (TL s.contexts) >= 1`
       by (Cases_on `TL s.contexts` >> fs[])
  >> `?parent rest. TL s.contexts = parent :: rest`
       by (Cases_on `TL s.contexts` >> fs[])
  >> `r'.contexts <> []` by fs[same_frame_rel_def]
  >> `TL r'.contexts = TL s.contexts /\ SND (HD r'.contexts) = SND (HD s.contexts)`
       by fs[same_frame_rel_def]
  >> `r'.contexts = (FST (HD r'.contexts), SND (HD s.contexts)) :: parent :: rest`
       by (Cases_on `r'.contexts` >> fs[] >> Cases_on `h` >> fs[])
  >> `LENGTH s'.contexts < LENGTH r'.contexts` by decide_tac
  (* Use paired lemma. Split its disjunction into two separate subgoals
     via strip_assume_tac, avoiding gvs contamination.
     DISJ1(r'): storage s'.rollback = storage r'.rollback
     DISJ2(r'): storage s'.rollback = storage (SND (HD r'.contexts)) *)
  >> Cases_on`y`
  >- (
    gvs[bind_def,get_current_context_def,return_def,fail_def]
    >> Cases_on`∃op. step_inst op s = (INR NONE, r')`
    >- (
      gvs[] >>
      drule_all step_inst_inr_preserves_storage >> rw[] >>
      drule_at_then(Pat`handle_step`)drule
        handle_step_pop_generic_gen_paired >>
      simp[] >>
      Cases_on`s.contexts` >> gvs[] >>
      disch_then (qx_choosel_then [`new_head`] strip_assume_tac) >>
      gvs[lookup_storage_def, FUN_EQ_THM] >>
      gvs[SUBSET_DEF,same_frame_rel_def] )
    >> gvs[COND_RATOR,AllCaseEqs()]
    >> gvs[option_CASE_rator, AllCaseEqs()]
    >> gvs[ignore_bind_def,bind_def,AllCaseEqs()]
    >> drule inc_pc_or_jump_inr_eq >> rw[] )
  >> gvs[handle_step_def]
  >> gvs[COND_RATOR,CaseEq"bool",reraise_def]
  >> gvs[handle_def,CaseEq"prod"]
  >> gvs[handle_create_reraises_when_some]
  >> gvs[reraise_def]
  >> reverse(Cases_on`x = Reverted`)
  >- (
    drule_at(Pat`handle_exception`)handle_exception_pop_failure_rollback_gen >>
    simp[] >> Cases_on`r'.contexts` >> gvs[] >>
    Cases_on`h` >> gvs[] >> Cases_on`s'.contexts` >> gvs[] >>
    Cases_on`h` >> gvs[] >> strip_tac >>
    gvs[same_frame_rel_def] >>
    Cases_on`s.contexts` >> fs[] >>
    BasicProvers.VAR_EQ_TAC >> fs[] >>
    drule_at(Pat`handle_exception`)handle_exception_pop_generic_gen >>
    simp[] )
  >> drule_at(Pat`handle_exception`)handle_exception_pop_generic_gen
  >> simp[]
  >> Cases_on`r'.contexts` >> gvs[]
  >> Cases_on`h` >> gvs[]
  >> rpt strip_tac >> gvs[]
  >- (
    qexists_tac`parent` >> gvs[] >>
    gvs[same_frame_rel_def] >>
    Cases_on`s.contexts` >> fs[] >>
    disj1_tac >> qx_gen_tac`a` >>
    qmatch_asmsub_abbrev_tac`callee_local_changes callee` >>
    reverse(Cases_on`a = callee`) >- (
      gvs[callee_local_changes_def] ) >>
    gvs[bind_def,get_current_context_def,return_def,AllCaseEqs()] >>
    Cases_on`∃op. step_inst op s = (INR (SOME Reverted),r')`
    >- (
      gvs[] >>
      drule step_inst_inr_preserves_storage >>
      simp[lookup_storage_def, FUN_EQ_THM] ) >>
    gvs[COND_RATOR,AllCaseEqs()] >>
    gvs[option_CASE_rator,AllCaseEqs()] >>
    gvs[ignore_bind_def,bind_def,AllCaseEqs()] >>
    drule inc_pc_or_jump_inr_eq >> rw[]) >>
  Cases_on`s.contexts` >> fs[]
QED

(* -------------------------------------------------------------------------
 * Single-step preservation of run_call_inv.
 *
 * Strategy: case on the length change. In each case, characterise
 * the previous invariant.
 * ------------------------------------------------------------------------- *)

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
  >> `wf_state s0` by fs[run_call_inv_def]
  >> `wf_state s1` by metis_tac[step_preserves_wf_state, SND]
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
    >> `s1.contexts ≠ []` by (strip_tac >> gvs[])
    >> `outputTo_consistent_stack s1` by (
         simp[outputTo_consistent_stack_def]
         >> Cases_on`s1.contexts` >> gvs[]
         >> simp[EVERY_MEM, MEM_EL, PULL_EXISTS]
         >> qx_gen_tac`i` >> strip_tac
         >> first_x_assum(qspec_then`i`mp_tac)
         >> simp[EL_CONS,PRE_SUB1,EL_MAP]
         >> gvs[outputTo_consistent_stack_def,EVERY_MEM,MEM_EL,
                PULL_EXISTS,EL_MAP])
    >> simp[]
    >> qabbrev_tac`ed = LENGTH es.contexts`
    >> qabbrev_tac`m = LENGTH s1.contexts  - ed + 2`
    >> `storage_slot_preserved s1.rollback es.rollback` by (
      rw[storage_slot_preserved_def] >>
      gvs[SUBSET_DEF, finite_setTheory.fIN_IN] >>
      gvs[run_call_inv_def, active_rollbacks_def] >>
      gvs[storage_slot_preserved_def] >>
      first_x_assum irule >>
      simp[finite_setTheory.fIN_IN] >>
      metis_tac[] )
    (* Now prove EVERY storage_slot_preserved for active_rollbacks *)
    >> simp[active_rollbacks_def]
    >> `¬(LENGTH s1.contexts < ed)` by simp[Abbr`ed`]
    >> simp[EVERY_EL, EL_MAP]
    >> rpt strip_tac
    >> Cases_on `n = 0`
    >- (
      (* n = 0: SND (EL 0 s1.contexts) has storage = s0.rollback storage *)
      gvs[]
      >> `storage_slot_preserved s0.rollback es.rollback`
           by (fs[run_call_inv_def, active_rollbacks_def])
      >> last_x_assum (qspec_then `0` mp_tac) >> simp[]
      >> strip_tac
      >> gvs[storage_slot_preserved_def]
      >> `0 < m` by (Cases_on`m` >> gvs[])
      >> simp[HD_TAKE]
      >> rpt strip_tac
      >> first_x_assum irule
      >> gvs[SUBSET_DEF, finite_setTheory.fIN_IN]
      >> Cases_on`s1.contexts` >> gvs[]
      >> strip_tac
      >> first_x_assum(qspec_then`0`(fn th => mp_tac th >> impl_tac >- gvs[]
            >> IF_CASES_TAC)) >> rw[]
      >> metis_tac[])
    >> (
      (* n > 0: SND (EL n s1.contexts) has storage = SND (EL (n-1) s0.contexts) storage *)
      last_x_assum (qspec_then `n` mp_tac) >> simp[]
      >> gvs[LENGTH_TAKE_EQ]
      >> strip_tac
      >> simp[EL_TAKE]
      >> gvs[run_call_inv_def, active_rollbacks_def]
      >> gvs[EVERY_EL, EL_MAP, LENGTH_TAKE_EQ]
      >> last_x_assum(qspec_then`n-1`mp_tac)
      >> simp[EL_TAKE]
      >> strip_tac
      >> gvs[storage_slot_preserved_def]
      >> rpt strip_tac
      >> gvs[EL_TAKE]
      >> gvs[MIN_DEF]
      >> Cases_on`s0.contexts` >> gvs[ADD1]
      >> Cases_on`es.contexts` >> gvs[Abbr`ed`,ADD1]
      >> Cases_on`n` >> gvs[ADD1]
      >> qmatch_asmsub_rename_tac`n < LENGTH t`
      >> last_x_assum(qspec_then`n + 1`mp_tac)
      >> simp[SUBSET_DEF] >> gvs[finite_setTheory.fIN_IN]
      >> disch_then(qspec_then`SK a k`mp_tac) >> simp[] >> strip_tac
      >> first_x_assum(qspecl_then[`a`,`k`]mp_tac)
      >> Cases_on`n` >> gvs[]
      >> simp[EL_TAKE,EL_CONS]))
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
    >> gvs[MIN_DEF] >> rw[] >> gvs[ADD1,Abbr`ed`]
    >> Cases_on`es.contexts` >> gvs[ADD1]
    >> Cases_on`rest` >> Cases_on`t` >> gvs[ADD1]
  )
QED

(* -------------------------------------------------------------------------
 * Main run_call preservation theorem.
 * ------------------------------------------------------------------------- *)

Theorem run_call_preserves_inv:
  ∀es res es'.
    outputTo_consistent_stack es ∧ wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
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
    outputTo_consistent_stack es ∧ wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
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
    outputTo_consistent_stack es ∧ wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
    run_call es = SOME (r, es') ⇒
    es'.txParams = es.txParams
Proof
  rpt strip_tac
  >> drule_all run_call_preserves_inv
  >> rw[run_call_inv_def]
QED

(* ---------------------------------------------------------------------
 * Single-context entry corollary. At entry to run_call with a single
 * context (the standard top-level transaction case), most preconditions
 * are trivially satisfied: SND (HD es.contexts) = es.rollback makes
 * storage_slot_preserved reflexive, and initial_context gives
 * jumpDest = NONE.
 * --------------------------------------------------------------------- *)

Theorem run_call_preserves_storage_outside_accessed_slots_single:
    outputTo_consistent_ctx ctx ∧
    wf_context ctx ∧
    wf_accounts es.rollback.accounts ∧
    ctx.jumpDest = NONE ∧
    es.contexts = [(ctx, es.rollback)] ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage
Proof
  rpt strip_tac
  >> irule run_call_preserves_storage_outside_accessed_slots
  >> gvs[outputTo_consistent_stack_def]
  >> simp[storage_slot_preserved_def]
  >> gvs[wf_state_def, all_accounts_def]
  >> gs[stack_room_ok_def, gas_stack_ok_def]
QED

Theorem run_call_preserves_storage_outside_accessed_slots_initial:
    es.contexts = [(initial_context callee code static rd t, es.rollback)] ∧
    wf_accounts es.rollback.accounts ∧
    (∀a. rd = Code a ⇒ callee = a) ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage
Proof
  rpt strip_tac
  >> irule run_call_preserves_storage_outside_accessed_slots_single
  >> gvs[]
  >> simp[outputTo_consistent_ctx_def, initial_msg_params_def]
QED

Theorem run_call_preserves_txParams_single:
  ∀es r es'.
    outputTo_consistent_ctx ctx ∧ wf_context ctx ∧
    wf_accounts es.rollback.accounts ∧
    ctx.jumpDest = NONE ∧
    es.contexts = [(ctx,es.rollback)] ∧
    run_call es = SOME (r, es') ⇒
    es'.txParams = es.txParams
Proof
  rpt strip_tac
  >> irule run_call_preserves_txParams
  >> gvs[storage_slot_preserved_def]
  >> gvs[outputTo_consistent_stack_def, wf_state_def, all_accounts_def]
  >> gs[gas_stack_ok_def, stack_room_ok_def]
QED

Theorem run_call_eq_run_single_context:
  LENGTH es.contexts = 1 ⇒
  run_call es = run es
Proof
  rw[run_call_def,run_def] >>
  simp[OWHILE_def] >>
  qho_match_abbrev_tac`COND (∃n. P1 n es) _ _ = COND (∃n. P2 n es) _ _` >>
  simp[] >>
  `∀n es. LENGTH es.contexts ≥ 1 ⇒ P1 n es = P2 n es` by (
    Induct >> simp[Abbr`P1`,Abbr`P2`] >>
    simp[FUNPOW_SUC] >> rpt strip_tac >> gvs[] >>
    first_x_assum drule >> pairarg_tac >> gvs[] >>
    pairarg_tac >> gvs[] >>
    qmatch_asmsub_rename_tac`step s1 = (_,s2)` >>
    qmatch_asmsub_rename_tac`_ (_,s0) = (_,s1)` >>
    `s0.contexts <> []` by (strip_tac >> gvs[]) >>
    `s1.contexts <> []` by (
      qmatch_asmsub_abbrev_tac`FUNPOW f m x` >>
      `(λp. (SND p).contexts ≠ []) (FUNPOW f m x)` suffices_by rw[] >>
      irule FUNPOW_invariant >> rw[Abbr`f`,Abbr`x`] >>
      irule step_preserves_nonempty_contexts >> rw[] ) >>
    `s2.contexts <> []` by (
      drule step_preserves_nonempty_contexts >> rw[] ) >>
    Cases_on`LENGTH s1.contexts` >> gvs[] >>
    Cases_on`LENGTH s2.contexts` >> gvs[] ) >>
  gvs[]
QED
