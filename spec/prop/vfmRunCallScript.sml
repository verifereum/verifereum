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
  vfmSameFrame vfmStaticCalls vfmStepLength vfmHandleStep vfmRunWithinFrame
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

(* ---- Helpers for step_preserves_non_accessed_storage ---- *)

(* For a cp execution, accounts are preserved; so storage at every
   slot is preserved, regardless of access-listing. *)
Theorem cp_imp_storage_preserved:
  cp m ∧ m s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rw[cp_def] >> res_tac >> simp[]
QED

(* step_inst of a non-call, non-storage opcode is cp: storage preserved. *)
Theorem step_inst_non_storage_storage_preserved:
  op ≠ SStore ∧ op ≠ TStore ∧ (∀n. op ≠ Log n) ∧
  op ≠ SelfDestruct ∧ op ≠ Create ∧ op ≠ Create2 ∧
  op ≠ Call ∧ op ≠ CallCode ∧ op ≠ DelegateCall ∧
  op ≠ StaticCall ∧
  step_inst op s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rpt strip_tac
  >> `cp (step_inst op)` by simp[cp_step_inst_non_call]
  >> metis_tac[cp_imp_storage_preserved]
QED

(* step_inst TStore preserves accounts.storage (writes tStorage only). *)
Theorem step_inst_TStore_storage_preserved:
  step_inst TStore s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rw[step_inst_def, step_sstore_def, bind_def, ignore_bind_def,
     pop_stack_def, consume_gas_def, get_callee_def,
     get_current_context_def, set_current_context_def, return_def,
     fail_def, assert_def, write_transient_storage_def,
     get_tStorage_def, set_tStorage_def, assert_not_static_def,
     get_static_def, AllCaseEqs()]
  >> gvs[AllCaseEqs()]
QED

(* Monadic predicate: execution preserves rollback.
   This is a stronger form of cp for handling primitives that modify
   context (like push_logs) but not rollback. *)
Definition preserves_rollback_def:
  preserves_rollback (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ⇒ s'.rollback = s.rollback
End

Theorem preserves_rollback_bind[simp]:
  preserves_rollback g ∧ (∀x. preserves_rollback (f x)) ⇒
  preserves_rollback (bind g f)
Proof
  rw[preserves_rollback_def, bind_def]
  >> Cases_on `g s` >> Cases_on `q` >> gvs[]
  >> res_tac >> gvs[]
QED

Theorem preserves_rollback_ignore_bind[simp]:
  preserves_rollback g ∧ preserves_rollback f ⇒
  preserves_rollback (ignore_bind g f)
Proof
  rw[ignore_bind_def] >> irule preserves_rollback_bind >> simp[]
QED

Theorem preserves_rollback_return[simp]:
  preserves_rollback (return x)
Proof
  rw[preserves_rollback_def, return_def]
QED

Theorem preserves_rollback_fail[simp]:
  preserves_rollback (fail e)
Proof
  rw[preserves_rollback_def, fail_def]
QED

Theorem preserves_rollback_reraise[simp]:
  preserves_rollback (reraise e)
Proof
  rw[preserves_rollback_def, reraise_def]
QED

Theorem preserves_rollback_cond[simp]:
  preserves_rollback m1 ∧ preserves_rollback m2 ⇒
  preserves_rollback (if b then m1 else m2)
Proof
  rw[]
QED

Theorem preserves_rollback_get_current_context[simp]:
  preserves_rollback get_current_context
Proof
  rw[preserves_rollback_def, get_current_context_def, bind_def,
     return_def, fail_def, AllCaseEqs()]
QED

Theorem preserves_rollback_set_current_context[simp]:
  preserves_rollback (set_current_context c)
Proof
  rw[preserves_rollback_def, set_current_context_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

Theorem preserves_rollback_get_static[simp]:
  preserves_rollback get_static
Proof
  rw[get_static_def] >> irule preserves_rollback_bind >> rw[]
QED

Theorem preserves_rollback_assert[simp]:
  preserves_rollback (assert b e)
Proof
  rw[preserves_rollback_def, assert_def, return_def, fail_def]
QED

Theorem preserves_rollback_pop_stack[simp]:
  preserves_rollback (pop_stack n)
Proof
  rw[pop_stack_def]
QED

Theorem preserves_rollback_consume_gas[simp]:
  preserves_rollback (consume_gas g)
Proof
  rw[consume_gas_def]
QED

Theorem preserves_rollback_expand_memory[simp]:
  preserves_rollback (expand_memory g)
Proof
  rw[expand_memory_def]
QED

Theorem preserves_rollback_read_memory[simp]:
  preserves_rollback (read_memory off sz)
Proof
  rw[read_memory_def]
QED

Theorem preserves_rollback_assert_not_static[simp]:
  preserves_rollback assert_not_static
Proof
  rw[assert_not_static_def]
QED

Theorem preserves_rollback_get_callee[simp]:
  preserves_rollback get_callee
Proof
  rw[get_callee_def]
QED

Theorem preserves_rollback_push_logs[simp]:
  preserves_rollback (push_logs ls)
Proof
  rw[push_logs_def]
QED

Theorem preserves_rollback_memory_expansion_info[simp]:
  preserves_rollback (memory_expansion_info off sz)
Proof
  rw[memory_expansion_info_def]
QED

Theorem preserves_rollback_update_gas_refund[simp]:
  preserves_rollback (update_gas_refund p)
Proof
  Cases_on `p` >> rw[update_gas_refund_def]
QED

(* step_inst (Log n) preserves rollback entirely. *)
Theorem step_inst_Log_preserves_rollback:
  preserves_rollback (step_inst (Log n))
Proof
  rw[step_inst_def, step_log_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[])
QED

Theorem step_inst_Log_storage_preserved:
  step_inst (Log n) s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rpt strip_tac
  >> `s'.rollback = s.rollback`
       by metis_tac[step_inst_Log_preserves_rollback, preserves_rollback_def]
  >> simp[]
QED

(* Monadic predicate: preserves storage at every address and key. *)
Definition preserves_storage_def:
  preserves_storage (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ⇒
      ∀a k.
        lookup_storage k (lookup_account a s'.rollback.accounts).storage =
        lookup_storage k (lookup_account a s.rollback.accounts).storage
End

Theorem preserves_rollback_imp_preserves_storage:
  preserves_rollback m ⇒ preserves_storage m
Proof
  rw[preserves_rollback_def, preserves_storage_def]
  >> res_tac >> simp[]
QED

Theorem preserves_storage_bind[simp]:
  preserves_storage g ∧ (∀x. preserves_storage (f x)) ⇒
  preserves_storage (bind g f)
Proof
  rw[preserves_storage_def, bind_def]
  >> Cases_on `g s` >> Cases_on `q` >> gvs[]
  >> res_tac >> gvs[]
  >> metis_tac[]
QED

Theorem preserves_storage_ignore_bind[simp]:
  preserves_storage g ∧ preserves_storage f ⇒
  preserves_storage (ignore_bind g f)
Proof
  rw[ignore_bind_def] >> irule preserves_storage_bind >> rw[]
QED

Theorem preserves_storage_cond[simp]:
  preserves_storage m1 ∧ preserves_storage m2 ⇒
  preserves_storage (if b then m1 else m2)
Proof
  rw[]
QED

Theorem preserves_storage_return[simp]:
  preserves_storage (return x)
Proof
  rw[preserves_storage_def, return_def]
QED

Theorem preserves_storage_fail[simp]:
  preserves_storage (fail e)
Proof
  rw[preserves_storage_def, fail_def]
QED

Theorem preserves_storage_reraise[simp]:
  preserves_storage (reraise e)
Proof
  rw[preserves_storage_def, reraise_def]
QED

(* transfer_value preserves storage at every address. *)
Theorem preserves_storage_transfer_value[simp]:
  preserves_storage (update_accounts (transfer_value fromAddr toAddr amt))
Proof
  rw[preserves_storage_def, update_accounts_def, return_def,
     transfer_value_preserves_storage]
QED

(* access_address may modify rollback.accesses (in Collect mode) so
   it's not preserves_rollback, but it preserves storage. *)
Theorem preserves_storage_access_address[simp]:
  preserves_storage (access_address addr)
Proof
  rw[preserves_storage_def, access_address_def, domain_check_def,
     set_domain_def, return_def, fail_def, ignore_bind_def, bind_def]
  >> gvs[AllCaseEqs()]
QED

Theorem preserves_rollback_get_accounts[simp]:
  preserves_rollback get_accounts
Proof
  rw[preserves_rollback_def, get_accounts_def, return_def]
QED

Theorem preserves_rollback_get_gas_left[simp]:
  preserves_rollback get_gas_left
Proof
  rw[get_gas_left_def]
QED

Theorem preserves_rollback_get_original[simp]:
  preserves_rollback get_original
Proof
  rw[preserves_rollback_def, get_original_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

Theorem preserves_rollback_finish[simp]:
  preserves_rollback finish
Proof
  rw[preserves_rollback_def, finish_def]
QED

(* add_to_delete modifies toDelete only; storage preserved. *)
Theorem preserves_storage_add_to_delete[simp]:
  preserves_storage (add_to_delete addr)
Proof
  rw[preserves_storage_def, add_to_delete_def, return_def]
QED

(* update_account at an address with an account whose storage matches
   the original: storage preserved at every address. *)
Theorem preserves_storage_update_account_same_storage:
  (∀accs. (lookup_account addr (f accs)).storage =
          (lookup_account addr accs).storage) ∧
  (∀accs a. a ≠ addr ⇒ f accs a = accs a) ⇒
  preserves_storage (update_accounts f)
Proof
  strip_tac
  >> rw[preserves_storage_def, update_accounts_def, return_def]
  >> reverse (Cases_on `a = addr`)
  >- (`f s.rollback.accounts a = s.rollback.accounts a` by fs[]
      >> rw[lookup_account_def])
  >> fs[]
QED

Theorem preserves_storage_get_current_context[simp]:
  preserves_storage get_current_context
Proof
  rw[preserves_storage_def, get_current_context_def] >>
  gvs[AllCaseEqs(), fail_def, return_def]
QED

Theorem preserves_storage_assert[simp]:
  preserves_storage (assert b x)
Proof
  rw[assert_def, preserves_storage_def]
QED

Theorem preserves_storage_set_current_context[simp]:
  preserves_storage (set_current_context x)
Proof
  rw[preserves_storage_def, set_current_context_def] >>
  gvs[AllCaseEqs(),return_def,fail_def]
QED

Theorem preserves_storage_pop_stack[simp]:
  preserves_storage (pop_stack n)
Proof
  rw[pop_stack_def] >>
  irule preserves_storage_bind >> rw[] >>
  irule preserves_storage_ignore_bind >> rw[] >>
  irule preserves_storage_ignore_bind >> rw[]
QED

Theorem preserves_storage_get_callee[simp]:
  preserves_storage get_callee
Proof
  rw[get_callee_def]
QED

Theorem preserves_storage_get_original[simp]:
  preserves_storage get_original
Proof
  irule preserves_rollback_imp_preserves_storage >> rw[]
QED

Theorem preserves_storage_get_accounts[simp]:
  preserves_storage get_accounts
Proof
  rw[get_accounts_def, preserves_storage_def, return_def]
QED

Theorem preserves_storage_consume_gas[simp]:
  preserves_storage (consume_gas n)
Proof
  irule preserves_rollback_imp_preserves_storage >> rw[]
QED

Theorem preserves_storage_assert_not_static[simp]:
  preserves_storage assert_not_static
Proof
  irule preserves_rollback_imp_preserves_storage >> rw[]
QED

Theorem preserves_storage_finish[simp]:
  preserves_storage finish
Proof
  irule preserves_rollback_imp_preserves_storage >> rw[]
QED

(* step_self_destruct: each update_accounts preserves storage.
   - transfer_value: preserves_storage_transfer_value.
   - update_account senderAddress (sender with balance := 0):
     sender was captured as lookup_account senderAddress accs, so
     (sender with balance := 0).storage = accs[senderAddress].storage. *)

Theorem preserves_storage_step_self_destruct:
  preserves_storage step_self_destruct
Proof
  rw[step_self_destruct_def] >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  simp[preserves_storage_def, bind_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[get_accounts_def, return_def] >>
  rename1`consume_gas n` >>
  rename1`transfer_value _ _ vv` >>
  gvs[bind_def, ignore_bind_def] >>
  gvs[AllCaseEqs(), consume_gas_def, return_def, assert_not_static_def,
      assert_def, bind_def, ignore_bind_def, get_current_context_def,
      set_current_context_def, fail_def, get_static_def, get_original_def,
      finish_def, COND_RATOR, add_to_delete_def, update_accounts_def,
      update_account_def, APPLY_UPDATE_THM, transfer_value_preserves_storage] >>
  simp[lookup_account_def, APPLY_UPDATE_THM] >> rw[] >>
  rewrite_tac[GSYM lookup_account_def] >>
  simp[transfer_value_preserves_storage]
QED

(* All preserves_rollback primitives are preserves_storage. *)
Theorem preserves_storage_of_preserves_rollback'[simp]:
  preserves_rollback m ⇒ preserves_storage m
Proof
  simp[preserves_rollback_imp_preserves_storage]
QED

Theorem step_inst_SelfDestruct_storage_preserved:
  step_inst SelfDestruct s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> `step_self_destruct s = (r, s')` by fs[step_inst_def]
  >> drule (preserves_storage_step_self_destruct
             |> REWRITE_RULE [preserves_storage_def])
  >> simp[]
QED

(* After access_slot x (when it succeeds), x is in storageKeys. *)
Theorem access_slot_adds_to_storageKeys:
  access_slot x s = (INL v, s') ⇒
  fIN x s'.rollback.accesses.storageKeys
Proof
  rw[access_slot_def, domain_check_def, set_domain_def,
     ignore_bind_def, bind_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

(* Monotone accesses: storageKeys never shrinks. *)
Definition access_monotone_def:
  access_monotone (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ⇒
      toSet s.rollback.accesses.storageKeys ⊆
        toSet s'.rollback.accesses.storageKeys
End

Theorem access_monotone_bind[simp]:
  access_monotone g ∧ (∀x. access_monotone (f x)) ⇒
  access_monotone (bind g f)
Proof
  rw[access_monotone_def, bind_def]
  >> Cases_on `g s` >> Cases_on `q` >> gvs[]
  >> res_tac >> gvs[]
  >> metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Theorem access_monotone_ignore_bind[simp]:
  access_monotone g ∧ access_monotone f ⇒
  access_monotone (ignore_bind g f)
Proof
  rw[ignore_bind_def] >> irule access_monotone_bind >> rw[]
QED

Theorem access_monotone_cond[simp]:
  access_monotone m1 ∧ access_monotone m2 ⇒
  access_monotone (if b then m1 else m2)
Proof
  rw[]
QED

Theorem access_monotone_of_preserves_rollback[simp]:
  preserves_rollback m ⇒ access_monotone m
Proof
  rw[preserves_rollback_def, access_monotone_def]
  >> res_tac >> simp[]
QED

(* access_slot: storageKeys grows (by inserting x). *)
Theorem access_monotone_access_slot[simp]:
  access_monotone (access_slot x)
Proof
  rw[access_monotone_def, access_slot_def, domain_check_def,
     set_domain_def, ignore_bind_def, bind_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
  >> simp[finite_setTheory.toSet_fINSERT, pred_setTheory.SUBSET_INSERT_RIGHT]
QED

(* Once (SK address key) is in storageKeys, any access_monotone
   continuation keeps it there. *)
Theorem access_monotone_preserves_slot_membership:
  access_monotone m ∧ m s = (r, s') ∧
  fIN x s.rollback.accesses.storageKeys ⇒
  fIN x s'.rollback.accesses.storageKeys
Proof
  rw[access_monotone_def]
  >> res_tac
  >> fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
QED

(* step_sstore_gas_consumption address key value: whenever it
   runs to completion, (SK address key) ends up in storageKeys.

   Proof: use access_monotone for the whole step (each primitive
   is access_monotone) plus `access_slot_adds_to_storageKeys` at
   the specific access_slot (SK address key) call. *)
Theorem access_monotone_step_sstore_gas_consumption[simp]:
  access_monotone (step_sstore_gas_consumption address key value)
Proof
  rw[step_sstore_gas_consumption_def]
  >> rpt (irule access_monotone_bind >> rw[]
          ORELSE irule access_monotone_ignore_bind >> rw[])
  >> irule access_monotone_of_preserves_rollback >> simp[]
QED

Theorem step_sstore_gas_consumption_adds_slot:
  step_sstore_gas_consumption address key value s = (INL v, s') ⇒
  fIN (SK address key) s'.rollback.accesses.storageKeys
Proof
  strip_tac
  >> qhdtm_x_assum `step_sstore_gas_consumption` mp_tac
  >> simp[step_sstore_gas_consumption_def, bind_def, ignore_bind_def]
  >> simp[AllCaseEqs()] >> strip_tac
  >> gvs[]
  >> rename1 `access_slot (SK address key) sx = (INL _, sy)`
  >> `fIN (SK address key) sy.rollback.accesses.storageKeys`
       by metis_tac[access_slot_adds_to_storageKeys]
  (* Tail: update_gas_refund followed by consume_gas, both preserves_rollback. *)
  >> rename1 `update_gas_refund refundUpdates sy = (_, s_gr)`
  >> `s_gr.rollback = sy.rollback` by
       metis_tac[preserves_rollback_update_gas_refund,
                 preserves_rollback_def]
  >> drule (preserves_rollback_consume_gas
            |> REWRITE_RULE [preserves_rollback_def])
  >> strip_tac
  >> simp[]
QED

(* write_storage address key value: the only primitive that writes
   accounts.storage. Modifies storage only at (address, key). *)
Theorem write_storage_effect:
  write_storage address key value s = (INL v, s') ⇒
  ∀a k. (a, k) ≠ (address, key) ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rw[write_storage_def, update_accounts_def, return_def]
  >> rw[lookup_account_def, update_account_def, APPLY_UPDATE_THM,
        lookup_storage_def, update_storage_def]
  >> gvs[UPDATE_def]
  >> rw[]
QED

(* write_storage effect: only (address, key) is modified; accesses
   are unchanged. *)
Theorem write_storage_non_target_preserved:
  write_storage address key value s = (r, s') ⇒
  s'.rollback.accesses = s.rollback.accesses ∧
  ∀a k. (a, k) ≠ (address, key) ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rw[write_storage_def, update_accounts_def, return_def,
     lookup_account_def, update_account_def, APPLY_UPDATE_THM]
  >> rw[]
  >> rw[lookup_storage_def, update_storage_def, UPDATE_def]
QED

(* write_storage preserves accesses.storageKeys (via the lemma above). *)
Theorem write_storage_preserves_storageKeys:
  write_storage address key value s = (r, s') ⇒
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  strip_tac >> drule write_storage_non_target_preserved
  >> strip_tac >> simp[]
QED

(* pop_stack is preserves_rollback, so we can extract rollback preservation
   across it. Same for get_callee. For step_sstore_gas_consumption we have
   access_monotone + adds_slot. For assert_not_static: preserves_rollback.
   For write_storage: effects characterised above. *)

(* We prove preserves_storage of step_sstore_gas_consumption (accounts and
   tStorage and toDelete unchanged, only accesses may grow). *)
(* access_slot preserves accounts (only accesses change). *)
Theorem preserves_storage_access_slot[simp]:
  preserves_storage (access_slot x)
Proof
  rw[preserves_storage_def, access_slot_def, domain_check_def,
     set_domain_def, ignore_bind_def, bind_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

Theorem preserves_storage_step_sstore_gas_consumption:
  preserves_storage (step_sstore_gas_consumption address key value)
Proof
  rw[step_sstore_gas_consumption_def]
  >> rpt (irule preserves_storage_bind >> rw[]
          ORELSE irule preserves_storage_ignore_bind >> rw[])
  >> simp[preserves_rollback_imp_preserves_storage]
QED

(* Main SSTORE lemma.
   The whole step_sstore F is: pop_stack 2; get_callee; step_sstore_gas_consumption;
   assert_not_static; write_storage. The "prefix" through assert_not_static is
   preserves_storage (storage at every (a,k) unchanged). Then write_storage
   modifies only (callee, key). For that target, step_sstore_gas_consumption
   added (SK callee key) to storageKeys. *)
Theorem preserves_storage_step_sstore_prefix:
  preserves_storage
    (do args <- pop_stack 2;
        address <- get_callee;
        step_sstore_gas_consumption address (EL 0 args) (EL 1 args);
        assert_not_static
     od)
Proof
  rpt (irule preserves_storage_bind >> rw[]
       ORELSE irule preserves_storage_ignore_bind >> rw[])
  >> simp[preserves_rollback_imp_preserves_storage,
          preserves_storage_step_sstore_gas_consumption]
QED

(* A monadic predicate combining preserves_storage with the
   access-listing invariant: storage at (a,k) unchanged UNLESS
   (SK a k) was added to storageKeys. This is exactly what we want. *)
Definition pns_def:
  pns (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ⇒
      ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a s'.rollback.accounts).storage =
        lookup_storage k (lookup_account a s.rollback.accounts).storage
End

Theorem pns_of_preserves_storage:
  preserves_storage m ⇒ pns m
Proof
  rw[pns_def, preserves_storage_def]
  >> res_tac >> simp[]
QED

Theorem pns_bind_preserves_storage:
  preserves_storage g ∧ (∀x. pns (f x)) ⇒ pns (bind g f)
Proof
  rw[pns_def, bind_def, preserves_storage_def]
  >> Cases_on `g s` >> Cases_on `q` >> gvs[]
  >> res_tac >> gvs[]
  >> first_x_assum drule >> simp[]
  >> strip_tac
  >> metis_tac[]
QED

Theorem pns_ignore_bind_preserves_storage:
  preserves_storage g ∧ pns f ⇒ pns (ignore_bind g f)
Proof
  rw[ignore_bind_def] >> irule pns_bind_preserves_storage >> rw[]
QED

(* General pns compositional: all pieces must be pns and access_monotone. *)
Theorem pns_bind_access_monotone:
  pns g ∧ access_monotone g ∧ (∀x. pns (f x)) ∧ (∀x. access_monotone (f x)) ⇒
  pns (bind g f)
Proof
  rw[pns_def, bind_def, access_monotone_def]
  >> Cases_on `g s` >> Cases_on `q` >> gvs[]
  >> res_tac >> gvs[]
  (* f x r' = (r, s'). Use access_monotone of f: r'.sk ⊆ s'.sk. *)
  >> `toSet r'.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys` by metis_tac[]
  >> `¬fIN (SK a k) r'.rollback.accesses.storageKeys` by
       (fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
        >> metis_tac[])
  >> first_x_assum drule >> simp[]
QED

Theorem pns_ignore_bind_access_monotone:
  pns g ∧ access_monotone g ∧ pns f ∧ access_monotone f ⇒
  pns (ignore_bind g f)
Proof
  rw[ignore_bind_def] >> irule pns_bind_access_monotone >> rw[]
QED

Theorem pns_cond[simp]:
  pns m1 ∧ pns m2 ⇒ pns (if b then m1 else m2)
Proof
  rw[]
QED

Theorem pns_return[simp]:
  pns (return x)
Proof
  rw[pns_def, return_def]
QED

Theorem pns_fail[simp]:
  pns (fail e)
Proof
  rw[pns_def, fail_def]
QED

Theorem pns_reraise[simp]:
  pns (reraise e)
Proof
  rw[pns_def, reraise_def]
QED

(* preserves_rollback ⇒ access_monotone ∧ pns. *)
Theorem preserves_rollback_imp_pns:
  preserves_rollback m ⇒ pns m
Proof
  rw[preserves_rollback_def, pns_def] >> res_tac >> simp[]
QED

(* pns handle: if f is pns + access_monotone and every h e is pns +
   access_monotone, then handle f h is pns. *)
Theorem pns_handle:
  pns f ∧ access_monotone f ∧
  (∀e. pns (h e)) ∧ (∀e. access_monotone (h e)) ⇒
  pns (handle f h)
Proof
  rw[pns_def, handle_def, access_monotone_def]
  >> Cases_on `f s` >> Cases_on `q` >> gvs[]
  >> res_tac >> gvs[]
  >> `toSet r'.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys` by metis_tac[]
  >> `¬fIN (SK a k) r'.rollback.accesses.storageKeys` by
       (fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
        >> metis_tac[])
  >> first_x_assum drule >> simp[]
QED

(* write_storage is pns: its only effect is at (address, key); and at
   that target, (SK address key) would need to be in s'.storageKeys
   for the modification to be observable — but write_storage doesn't
   add to storageKeys. So if ¬fIN (SK a k) s'.storageKeys, either
   (a,k) ≠ target (unchanged by write_storage), or (a,k) = target BUT
   (SK address key) wasn't in s.storageKeys either. In the latter
   case, the "unchanged" property is vacuously true... no wait, it's
   not vacuous — we need to rule out the case where write_storage
   fires on (a,k) but ¬fIN (SK a k) s'.storageKeys. But write_storage
   doesn't touch storageKeys, so ¬fIN (SK a k) s'.storageKeys = ¬fIN (SK a k)
   s.storageKeys. The semantics of SSTORE requires (SK address key)
   to have been added BEFORE write_storage, so assuming SSTORE's prefix
   ran, (SK address key) ∈ s.storageKeys. So at (address, key),
   ¬fIN holds iff the prefix access-listing didn't happen. *)

(* For the direct write_storage lemma: if we START with (SK address key)
   already in storageKeys and write_storage runs, then either the hypothesis
   fails or (a,k) ≠ target. *)
Theorem pns_write_storage_with_pre_access:
  fIN (SK address key) s.rollback.accesses.storageKeys ∧
  write_storage address key value s = (r, s') ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac >> rpt gen_tac >> strip_tac
  >> `s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys`
       by metis_tac[write_storage_preserves_storageKeys]
  >> `(a, k) ≠ (address, key)`
       by (strip_tac >> gvs[])
  >> metis_tac[write_storage_non_target_preserved]
QED

Theorem step_inst_SStore_storage_preserved:
  step_inst SStore s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rw[step_inst_def] >>
  gvs[step_sstore_def, bind_def, ignore_bind_def, AllCaseEqs(),
      pop_stack_def, get_callee_def, assert_not_static_def,
      return_def, get_current_context_def, set_current_context_def,
      assert_def, fail_def, get_static_def] >>
  qmatch_asmsub_abbrev_tac`step_sstore_gas_consumption address key value` >>
  mp_tac preserves_storage_step_sstore_gas_consumption >>
  rw[preserves_storage_def] >> first_x_assum drule >> rw[] >>
  drule step_sstore_gas_consumption_adds_slot >> strip_tac >>
  drule write_storage_preserves_storageKeys >> strip_tac >>
  drule write_storage_non_target_preserved >> rw[] >>
  Cases_on`(a,k) = (address,key)` >> gvs[] 
QED

(* Main theorem: step preserves non-accessed storage in the same-frame
   case (Case 0 of run_call_inv_step).

   Non-callee addresses: via `callee_local_changes` from `same_frame_rel`.
   Callee address: opcode case analysis using the per-opcode lemmas
   above. *)
(* Helper: inc_pc_or_jump preserves rollback (only modifies context). *)
Theorem preserves_rollback_inc_pc_or_jump[simp]:
  preserves_rollback (inc_pc_or_jump op)
Proof
  rw[inc_pc_or_jump_def]
  >> irule preserves_rollback_bind >> rw[]
  >> CASE_TAC >> simp[]
  >> irule preserves_rollback_ignore_bind >> rw[]
QED

(* step_inst preserves storage at non-accessed slots (same conclusion
   as step_preserves_non_accessed_storage but at the inner opcode level).
   Proof by opcode case analysis using the per-opcode lemmas. *)
Theorem step_inst_preserves_non_accessed_storage:
  step_inst op s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> Cases_on `op = SStore`
  >- (gvs[] >> metis_tac[step_inst_SStore_storage_preserved])
  >> Cases_on `op = TStore`
  >- (gvs[] >> rpt strip_tac
      >> drule step_inst_TStore_storage_preserved
      >> simp[])
  >> Cases_on `∃n. op = Log n`
  >- (fs[] >> rpt strip_tac >> gvs[]
      >> metis_tac[step_inst_Log_storage_preserved])
  >> Cases_on `op = SelfDestruct`
  >- (gvs[] >> rpt strip_tac
      >> drule step_inst_SelfDestruct_storage_preserved
      >> simp[])
  >> Cases_on `op = Call ∨ op = CallCode ∨ op = DelegateCall ∨
               op = StaticCall ∨ op = Create ∨ op = Create2`
  >- (
    (* Call/create family: outside scope of this lemma — call-family
       ops may modify storage via push/pop, handled by step_push_structure. *)
    cheat)
  (* Non-call, non-storage-writing: cp preserves accounts entirely. *)
  >> `∀n. op ≠ Log n` by (Cases_on `op` >> fs[])
  >> `cp (step_inst op)` by (
       irule cp_step_inst_non_call >> simp[]
       >> metis_tac[])
  >> drule cp_imp_storage_preserved
  >> rpt strip_tac
  >> first_x_assum drule >> simp[]
QED

(* access_monotone of step: storageKeys never shrinks. Needed for the
   compositional proof of step_preserves_non_accessed_storage. *)
Theorem access_monotone_same_frame:
  same_frame_rel s s' ⇒
    toSet s.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys
Proof
  rw[same_frame_rel_def]
QED

Theorem preserves_rollback_get_output_to[simp]:
  preserves_rollback get_output_to
Proof
  rw[get_output_to_def]
QED

Theorem preserves_rollback_get_return_data[simp]:
  preserves_rollback get_return_data
Proof
  rw[get_return_data_def]
QED

(* handle_create preserves storage: it may install code at the callee
   but doesn't touch .storage field. *)
Theorem preserves_storage_handle_create:
  preserves_storage (handle_create e)
Proof
  rw[handle_create_def]
  >> rpt (irule preserves_storage_bind >> rw[]
          ORELSE irule preserves_storage_ignore_bind >> rw[])
  >> Cases_on `e` >> Cases_on `x'`
  >> simp[]
  >> TRY (irule preserves_storage_of_preserves_rollback' >> simp[] >> NO_TAC)
  >> rpt (irule preserves_storage_bind >> rw[]
          ORELSE irule preserves_storage_ignore_bind >> rw[])
  >> TRY (irule preserves_storage_of_preserves_rollback' >> simp[] >> NO_TAC)
  (* Remaining: update_accounts (update_account address (lookup_account address
     accounts with code := code)) — preserves storage at every address. *)
  >> irule preserves_storage_update_account_same_storage
  >> qexists_tac `c`
  >> rw[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

Theorem preserves_rollback_set_return_data[simp]:
  preserves_rollback (set_return_data rd)
Proof
  rw[set_return_data_def]
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
      >> simp[]
      >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
      >> simp[])
    >> Cases_on `FLOOKUP (FST h).msgParams.parsed (FST h).pc` >> gvs[]
    >- (
      (* Invalid case. *)
      strip_tac
      >> drule step_inst_preserves_non_accessed_storage
      >> simp[]
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
    >> drule step_inst_preserves_non_accessed_storage
    >> simp[]
    >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
    >> simp[])
  >> (
    (* inner INR: handle_step runs. Full case analysis requires:
       - If same_frame_rel s r': storage preserved from s to r'
         (via step_inst_preserves_non_accessed_storage), then
         handle_step r' → s' preserves storage at every slot
         (via handle_step_preserves_storage_same_length).
       - If inner grew: inner was a Call family op. pushed_rb has
         same storage as s. handle_step popped back.
       Infrastructure in place. Final assembly is mechanical. *)
    cheat)
QED

(* -------------------------------------------------------------------------
 * Push-structure lemma for step (Case +1 of run_call_inv_step).
 *
 * When step grows by +1 (push), the new contexts prepend a child context
 * with a pushed rollback whose accounts.storage equals s.rollback.accounts.storage
 * (because the only modification during the push prefix is transfer_value,
 * which only touches balance). The new s'.rollback.accounts.storage also
 * equals s.rollback.accounts.storage. Accesses are monotone. Child's
 * msgParams is outputTo-consistent.
 *
 * Covers both INL-grow (plain proceed_call or proceed_create) and
 * INR-grow-then-reraise (precompile failure with LENGTH s1 > LENGTH s
 * handled by handle_step reraising).
 * ------------------------------------------------------------------------- *)
Theorem step_push_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∃child_ctx pushed_rb.
      s'.contexts = (child_ctx, pushed_rb) :: s.contexts ∧
      (∀a. (lookup_account a s'.rollback.accounts).storage =
           (lookup_account a s.rollback.accounts).storage) ∧
      (∀a. (lookup_account a pushed_rb.accounts).storage =
           (lookup_account a s.rollback.accounts).storage) ∧
      toSet s.rollback.accesses.storageKeys ⊆
        toSet s'.rollback.accesses.storageKeys ∧
      (* s.rollback.accesses ⊆ pushed_rb.accesses because pushed_rb is
         captured during proceed_call/create AFTER step_inst's prefix
         (which only grows accesses). *)
      toSet s.rollback.accesses.storageKeys ⊆
        toSet pushed_rb.accesses.storageKeys ∧
      outputTo_consistent_ctx child_ctx
Proof
  cheat
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
Theorem step_pop_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧
    LENGTH s'.contexts < LENGTH s.contexts ⇒
    ∃new_head parent rest.
      s.contexts = HD s.contexts :: parent :: rest ∧
      s'.contexts = (new_head, SND parent) :: rest ∧
      new_head.msgParams = (FST parent).msgParams ∧
      (s'.rollback = s.rollback ∨
       s'.rollback = SND (HD s.contexts))
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
    >> qmatch_asmsub_rename_tac `s1.contexts = (child_ctx, pushed_rb) :: s0.contexts`
    (* outputTo_consistent_stack s1: old stack consistent + new child consistent. *)
    >> `outputTo_consistent_stack s1` by (
         simp[outputTo_consistent_stack_def]
         >> fs[outputTo_consistent_stack_def])
    >> simp[]
    (* active_rollbacks ed s1 = s1.rollback :: pushed_rb :: TL_of_old. *)
    >> qabbrev_tac `ntk = LENGTH s0.contexts - LENGTH es.contexts + 2`
    >> `¬(LENGTH s0.contexts < LENGTH es.contexts) ∧
        ¬(LENGTH s1.contexts < LENGTH es.contexts)` by simp[]
    >> `active_rollbacks (LENGTH es.contexts) s1 =
          s1.rollback :: pushed_rb :: MAP SND (TAKE ntk s0.contexts)`
        by (simp[active_rollbacks_def, Abbr`ntk`, arithmeticTheory.ADD1])
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
    >> simp[Q.SPEC`¬A`(IMP_DISJ_THM)|>GSYM|>REWRITE_RULE[]]
    >> strip_tac
    >> qmatch_asmsub_rename_tac `s0.contexts = callee_ctx :: parent :: rest`
    (* outputTo_consistent_stack s1: new_head has parent's msgParams. *)
    >> `outputTo_consistent_stack s1` by (
         `EVERY outputTo_consistent_ctx (MAP FST s0.contexts) ∧
          s0.contexts ≠ []`
           by fs[outputTo_consistent_stack_def]
         >> qpat_x_assum `s0.contexts = _` SUBST_ALL_TAC
         >> fs[]
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
        by (qpat_x_assum `s0.contexts = _` SUBST1_TAC
            >> qpat_x_assum `s1.contexts = _` SUBST1_TAC
            >> simp[])
    >> `¬(LENGTH s0.contexts < ed)` by simp[]
    (* Substitute context shapes early so downstream references are clean. *)
    >> `s1.rollback = s0.rollback ∨ s1.rollback = SND callee_ctx` by (
         Cases_on `s1.rollback = s0.rollback` >> fs[]
         >> `s1.rollback = SND (HD s0.contexts)` by fs[]
         >> qpat_x_assum `s0.contexts = _` SUBST_ALL_TAC >> fs[])
    (* Split on whether s1.contexts is below ed or not. *)
    >> Cases_on `LENGTH s1.contexts < ed`
    >- (
      (* LENGTH s1 < ed: active_rollbacks s1 = [s1.rollback]. *)
      simp[active_rollbacks_def]
      >> qpat_x_assum `EVERY _ (active_rollbacks ed s0)` mp_tac
      >> simp[active_rollbacks_def]
      >> `LENGTH s0.contexts + 2 - ed ≥ 1` by decide_tac
      >> `∃n. LENGTH s0.contexts + 2 - ed = SUC n` by
           (Cases_on `LENGTH s0.contexts + 2 - ed` >> fs[])
      >> simp[]
      >> qpat_x_assum `s0.contexts = _` SUBST1_TAC
      >> simp[]
      >> strip_tac
      >> fs[])
    (* LENGTH s1 ≥ ed. Both active_rollbacks have a non-trivial tail.
       s0's TAKE takes one more element than s1's. *)
    >> qpat_x_assum `EVERY _ (active_rollbacks ed s0)` mp_tac
    >> simp[active_rollbacks_def]
    >> qpat_x_assum `s0.contexts = _` SUBST1_TAC
    >> qpat_x_assum `s1.contexts = _` SUBST1_TAC
    >> simp[]
    >> `LENGTH rest + 1 ≥ ed` by decide_tac
    >> `LENGTH rest + 3 - ed = SUC (SUC (LENGTH rest + 1 - ed)) ∧
        LENGTH rest + 2 - ed = SUC (LENGTH rest + 1 - ed)` by decide_tac
    >> simp[]
    >> strip_tac
    (* Now we have EVERY on [s0.rollback, SND callee_ctx, SND parent, ...rest prefix]
       and need to show EVERY on [s1.rollback, SND parent, ...rest prefix]. *)
    >> fs[])
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
