(* ==========================================================================
 * vfmStoragePredicatesScript.sml
 *
 * Monadic predicate frameworks for reasoning about what effects EVM
 * computations have on rollback, accounts.storage, and access-listing.
 *
 * Four monadic predicates, in increasing specificity:
 *   - preserves_rollback: execution does not modify s.rollback
 *   - preserves_storage:  execution preserves every account's .storage
 *   - access_monotone:     execution's access-list only grows
 *   - pns:                 execution preserves storage at slots not
 *                          added to the access-list (preserves non-
 *                          accessed storage)
 *
 * Each predicate is closed under monad combinators (bind, ignore_bind,
 * etc.), with [simp] composition rules and per-primitive leaves.
 *
 * Hierarchy:
 *   preserves_rollback ──► preserves_storage ──► pns
 *   preserves_rollback ──► access_monotone ──► pns (combined)
 *
 * This theory also proves:
 *   - Per-opcode storage/access-effect lemmas (SStore, TStore, Log,
 *     SelfDestruct).
 *   - The step_inst_preserves_non_accessed_storage lemma: the main
 *     per-opcode dispatch theorem combining pns with opcode case
 *     analysis.
 *   - Compound operation lemmas: handle_create, step_self_destruct,
 *     step_call, step_create, proceed_call, proceed_create, dispatch
 *     precompiles etc. all preserve storage.
 *   - Access-list effect lemmas: write_storage_effect, access_slot
 *     adds to storageKeys, step_sstore_gas_consumption adds the slot.
 * ========================================================================== *)
Theory vfmStoragePredicates
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list sum
  vfmState vfmContext vfmExecution vfmExecutionProp
  vfmStaticCalls vfmSameFrame
Libs
  dep_rewrite BasicProvers


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

Theorem preserves_rollback_imp_preserves_storage[simp]:
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
  step_inst op s = (r, s') ∧ s.contexts ≠ [] ∧ ¬is_call op
  ⇒
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
    gvs[is_call_def])
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
  >> TRY (irule preserves_rollback_imp_preserves_storage >> simp[] >> NO_TAC)
  >> rpt (irule preserves_storage_bind >> rw[]
          ORELSE irule preserves_storage_ignore_bind >> rw[])
  >> TRY (irule preserves_rollback_imp_preserves_storage >> simp[] >> NO_TAC)
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

(* =====================================================================
 * Additional primitive preserves_rollback / preserves_storage lemmas
 * needed for the call/create same-frame abort-path analysis.
 * ===================================================================== *)

Theorem preserves_rollback_push_stack[simp]:
  preserves_rollback (push_stack w)
Proof
  rw[preserves_rollback_def, push_stack_def, bind_def, ignore_bind_def,
     get_current_context_def, set_current_context_def, return_def,
     fail_def, assert_def]
  >> gvs[AllCaseEqs()]
QED

Theorem preserves_rollback_inc_pc[simp]:
  preserves_rollback inc_pc
Proof
  rw[preserves_rollback_def, inc_pc_def, bind_def,
     get_current_context_def, set_current_context_def, return_def,
     fail_def]
  >> gvs[AllCaseEqs()]
QED

Theorem preserves_rollback_unuse_gas[simp]:
  preserves_rollback (unuse_gas n)
Proof
  rw[preserves_rollback_def, unuse_gas_def, bind_def, ignore_bind_def,
     get_current_context_def, set_current_context_def, return_def,
     fail_def, assert_def]
  >> gvs[AllCaseEqs()]
QED

Theorem preserves_rollback_get_num_contexts[simp]:
  preserves_rollback get_num_contexts
Proof
  rw[preserves_rollback_def, get_num_contexts_def, return_def]
QED

Theorem preserves_rollback_get_value[simp]:
  preserves_rollback get_value
Proof
  rw[preserves_rollback_def, get_value_def, bind_def,
     get_current_context_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

Theorem preserves_rollback_get_caller[simp]:
  preserves_rollback get_caller
Proof
  rw[preserves_rollback_def, get_caller_def, bind_def,
     get_current_context_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

Theorem preserves_rollback_set_domain[simp]:
  preserves_rollback (set_domain d)
Proof
  rw[preserves_rollback_def, set_domain_def, return_def]
QED

Theorem preserves_rollback_ensure_storage_in_domain[simp]:
  preserves_rollback (ensure_storage_in_domain a)
Proof
  rw[preserves_rollback_def, ensure_storage_in_domain_def,
     domain_check_def, return_def, fail_def, ignore_bind_def,
     set_domain_def, bind_def]
  >> gvs[AllCaseEqs()]
QED

(* set_original modifies the last context's saved rollback, not the
   outer rollback field. So preserves_rollback holds trivially. *)
Theorem preserves_rollback_set_original[simp]:
  preserves_rollback (set_original a)
Proof
  rw[preserves_rollback_def, set_original_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

Theorem preserves_rollback_get_rollback[simp]:
  preserves_rollback get_rollback
Proof
  rw[preserves_rollback_def, get_rollback_def, return_def]
QED

Theorem preserves_rollback_abort_call_value[simp]:
  preserves_rollback (abort_call_value stipend)
Proof
  rw[abort_call_value_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[])
QED

Theorem preserves_rollback_abort_unuse[simp]:
  preserves_rollback (abort_unuse n)
Proof
  rw[abort_unuse_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[])
QED

(* update_accounts (increment_nonce a) only modifies .nonce, not .storage. *)
Theorem preserves_storage_update_accounts_increment_nonce[simp]:
  preserves_storage (update_accounts (increment_nonce a))
Proof
  irule preserves_storage_update_account_same_storage
  >> qexists_tac `a`
  >> rw[increment_nonce_def, update_account_def, lookup_account_def,
        combinTheory.APPLY_UPDATE_THM]
QED

Theorem preserves_storage_abort_create_exists[simp]:
  preserves_storage (abort_create_exists a)
Proof
  rw[abort_create_exists_def]
  >> rpt (irule preserves_storage_ignore_bind >> rw[]
          ORELSE irule preserves_storage_bind >> rw[])
QED

(* The composed update (transfer_value o increment_nonce) preserves
   storage because neither operation touches .storage. *)
Theorem preserves_storage_update_accounts_transfer_increment_nonce[simp]:
  preserves_storage
    (update_accounts
       (transfer_value sender recipient value o increment_nonce recipient))
Proof
  (* Both components only touch balance/nonce. The composed function
     agrees with the input at addresses outside {sender, recipient} on
     all fields including storage. *)
  rw[preserves_storage_def, update_accounts_def, return_def]
  >> rw[transfer_value_def, increment_nonce_def, update_account_def,
        lookup_account_def, combinTheory.APPLY_UPDATE_THM]
  >> rw[] >> gvs[AllCaseEqs()]
QED


(* =====================================================================
 * step_call / step_create: when they return INL at same frame length,
 * no proceed_{call,create} ran (which would strictly grow length), so
 * only abort paths took place. These all preserve storage.
 * ===================================================================== *)

(* preserves_rollback_get_call_data: needed for precompile lemmas. *)
Theorem preserves_rollback_get_call_data[simp]:
  preserves_rollback get_call_data
Proof
  rw[preserves_rollback_def, get_call_data_def, bind_def,
     get_current_context_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

(* Each precompile is preserves_rollback. *)
Theorem preserves_rollback_precompile_ecrecover[simp]:
  preserves_rollback precompile_ecrecover
Proof
  rw[precompile_ecrecover_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_identity[simp]:
  preserves_rollback precompile_identity
Proof
  rw[precompile_identity_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[])
QED

Theorem preserves_rollback_precompile_modexp[simp]:
  preserves_rollback precompile_modexp
Proof
  rw[precompile_modexp_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[])
QED

Theorem preserves_rollback_precompile_sha2_256[simp]:
  preserves_rollback precompile_sha2_256
Proof
  rw[precompile_sha2_256_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[])
QED

Theorem preserves_rollback_precompile_ripemd_160[simp]:
  preserves_rollback precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_ecadd[simp]:
  preserves_rollback precompile_ecadd
Proof
  rw[precompile_ecadd_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_ecmul[simp]:
  preserves_rollback precompile_ecmul
Proof
  rw[precompile_ecmul_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_ecpairing[simp]:
  preserves_rollback precompile_ecpairing
Proof
  rw[precompile_ecpairing_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_blake2f[simp]:
  preserves_rollback precompile_blake2f
Proof
  rw[precompile_blake2f_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_point_eval[simp]:
  preserves_rollback precompile_point_eval
Proof
  rw[precompile_point_eval_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_bls_g1add[simp]:
  preserves_rollback precompile_bls_g1add
Proof
  rw[precompile_bls_g1add_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_bls_g1msm[simp]:
  preserves_rollback precompile_bls_g1msm
Proof
  rw[precompile_bls_g1msm_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_bls_g2add[simp]:
  preserves_rollback precompile_bls_g2add
Proof
  rw[precompile_bls_g2add_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_bls_g2msm[simp]:
  preserves_rollback precompile_bls_g2msm
Proof
  rw[precompile_bls_g2msm_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_bls_pairing[simp]:
  preserves_rollback precompile_bls_pairing
Proof
  rw[precompile_bls_pairing_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_bls_map_fp_to_g1[simp]:
  preserves_rollback precompile_bls_map_fp_to_g1
Proof
  rw[precompile_bls_map_fp_to_g1_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_bls_map_fp2_to_g2[simp]:
  preserves_rollback precompile_bls_map_fp2_to_g2
Proof
  rw[precompile_bls_map_fp2_to_g2_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

Theorem preserves_rollback_precompile_p256verify[simp]:
  preserves_rollback precompile_p256verify
Proof
  rw[precompile_p256verify_def]
  >> rpt (irule preserves_rollback_bind >> rw[]
          ORELSE irule preserves_rollback_ignore_bind >> rw[]
          ORELSE CASE_TAC >> simp[])
QED

(* Precompiles are all preserves_rollback. *)
Theorem preserves_rollback_dispatch_precompiles[simp]:
  preserves_rollback (dispatch_precompiles a)
Proof
  rw[dispatch_precompiles_def]
QED

Theorem preserves_rollback_push_context[simp]:
  preserves_rollback (push_context crb)
Proof
  rw[preserves_rollback_def, push_context_def, return_def]
QED

Theorem preserves_storage_case_pair[simp]:
  (∀x y. preserves_storage (f x y)) ⇒
  preserves_storage (case p of (x, y) => f x y)
Proof
  Cases_on `p` >> rw[]
QED

Theorem preserves_storage_UNCURRY[simp]:
  (∀x y. preserves_storage (f x y)) ⇒
  preserves_storage (UNCURRY f p)
Proof
  Cases_on `p` >> rw[]
QED

Theorem preserves_storage_let[simp]:
  (∀x. preserves_storage (f x)) ⇒
  preserves_storage (let x = v in f x)
Proof
  rw[]
QED

Theorem preserves_storage_proceed_call[simp]:
  preserves_storage
    (proceed_call op sender address value argsOffset argsSize code stipend outputTo)
Proof
  simp[proceed_call_def]
  >> rpt (irule preserves_storage_bind >> rw[]
          ORELSE irule preserves_storage_ignore_bind >> rw[]
          ORELSE irule preserves_storage_cond >> rw[])
  >> simp[preserves_rollback_dispatch_precompiles, preserves_rollback_imp_preserves_storage]
QED

Theorem preserves_storage_proceed_create[simp]:
  preserves_storage
    (proceed_create senderAddress address value code cappedGas)
Proof
  simp[proceed_create_def]
  >> rpt (irule preserves_storage_bind >> rw[]
          ORELSE irule preserves_storage_ignore_bind >> rw[]
          ORELSE irule preserves_storage_cond >> rw[])
QED

Theorem preserves_storage_step_call:
  preserves_storage (step_call op)
Proof
  simp[step_call_def] >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  pairarg_tac >> simp[] >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  irule preserves_storage_bind >> simp[] >>
  reverse conj_tac >- ( CASE_TAC >> simp[] ) >>
  Cases >> simp[] >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  pairarg_tac >> simp[] >>
  irule preserves_storage_ignore_bind >> simp[] >>
  irule preserves_storage_ignore_bind >> simp[] >>
  irule preserves_storage_ignore_bind >> simp[] >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  irule preserves_storage_cond >> simp[]
QED

Theorem preserves_storage_step_create:
  preserves_storage (step_create two)
Proof
  simp[step_create_def] >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  irule preserves_storage_ignore_bind >> simp[] >>
  irule preserves_storage_ignore_bind >> simp[] >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  irule preserves_storage_ignore_bind >> simp[] >>
  irule preserves_storage_ignore_bind >> simp[] >>
  irule preserves_storage_bind >> simp[] >> gen_tac >>
  rpt(irule preserves_storage_ignore_bind >> simp[])
QED

Theorem step_call_same_frame_preserves_storage:
  step_call op s = (INL (), s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> metis_tac[preserves_storage_step_call, preserves_storage_def]
QED

Theorem step_create_same_frame_preserves_storage:
  step_create two s = (INL (), s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> metis_tac[preserves_storage_step_create, preserves_storage_def]
QED

(* Main dispatcher: is_call op + step_inst INL + same length ⇒ storage preserved. *)
Theorem is_call_same_frame_preserves_storage:
  is_call op ∧
  step_inst op s = (INL (), s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> Cases_on `op` >> fs[is_call_def, step_inst_def]
  >> (drule step_call_same_frame_preserves_storage ORELSE
      drule step_create_same_frame_preserves_storage ) >> rw[]
QED

(* step_inst returning INR preserves storage unconditionally.
   This is because write_storage (the only storage-modifying primitive)
   always succeeds, so if step_inst returns INR, write_storage didn't run.
   - For call/create ops: preserves_storage_step_call/create is unconditional
   - For SStore: if it fails, it's before write_storage
   - For other ops: they don't write storage at all (cp or preserves_storage) *)
Theorem step_inst_inr_preserves_storage:
  step_inst op s = (INR e, s') ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> Cases_on `is_call op`
  >- ((* Call/create: use preserves_storage_step_call/create *)
      Cases_on `op` >> gvs[is_call_def, step_inst_def]
      >> metis_tac[preserves_storage_step_call, preserves_storage_step_create,
                   preserves_storage_def])
  (* Non-call ops *)
  >> Cases_on `op = SStore`
  >- ((* SStore INR: failed before write_storage *)
      gvs[step_inst_def, step_sstore_def, bind_def, ignore_bind_def,
          AllCaseEqs(), pop_stack_def, get_callee_def, assert_not_static_def,
          return_def, get_current_context_def, set_current_context_def,
          assert_def, fail_def, get_static_def]
      (* Each failure case is before write_storage, so s' = some intermediate
         state that preserved storage. The gas consumption primitives
         preserve storage. *)
      >- ((* gas consumption INL but contexts empty - use gas consumption preservation *)
          drule (REWRITE_RULE[preserves_storage_def] preserves_storage_step_sstore_gas_consumption)
          >> simp[])
      >- ((* write_storage INR - impossible since write_storage always returns INL *)
          gvs[write_storage_def, update_accounts_def, return_def])
      >- ((* assert_not_static failed - s' from gas consumption *)
          drule (REWRITE_RULE[preserves_storage_def] preserves_storage_step_sstore_gas_consumption)
          >> simp[])
      (* gas consumption INR - s' from gas consumption *)
      >> drule (REWRITE_RULE[preserves_storage_def] preserves_storage_step_sstore_gas_consumption)
      >> simp[])
  >> Cases_on `op = TStore`
  >- (gvs[] >> drule step_inst_TStore_storage_preserved >> simp[])
  >> Cases_on `∃n. op = Log n`
  >- (gvs[] >> metis_tac[step_inst_Log_storage_preserved])
  >> Cases_on `op = SelfDestruct`
  >- (gvs[] >> drule step_inst_SelfDestruct_storage_preserved >> simp[])
  (* Remaining non-call, non-storage ops are cp *)
  >> `∀n. op ≠ Log n` by (Cases_on `op` >> fs[])
  >> `cp (step_inst op)` by (
       irule cp_step_inst_non_call >> simp[]
       >> Cases_on `op` >> gvs[is_call_def])
  >> metis_tac[cp_imp_storage_preserved]
QED
