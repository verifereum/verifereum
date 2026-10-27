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
  vfmStaticCalls vfmSameFrame vfmPreserves
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* step_inst TStore preserves accounts.storage (writes tStorage only). *)
Theorem step_inst_TStore_storage_preserved:
  step_inst TStore s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
QED

(* Monadic predicate: execution preserves rollback.
   This is a stronger form of cp for handling primitives that modify
   context (like push_logs) but not rollback. *)
Definition preserves_rollback_def:
  preserves_rollback (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ⇒ s'.rollback = s.rollback
End

Definition preserves_storage_def:
  preserves_storage (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ⇒
      ∀a k.
        lookup_storage k (lookup_account a s'.rollback.accounts).storage =
        lookup_storage k (lookup_account a s.rollback.accounts).storage
End

Definition access_monotone_def:
  access_monotone (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ⇒
      toSet s.rollback.accesses.storageKeys ⊆
        toSet s'.rollback.accesses.storageKeys
End

Definition pns_def:
  pns (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ⇒
      ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a s'.rollback.accounts).storage =
        lookup_storage k (lookup_account a s.rollback.accounts).storage
End

(* ================================================================== *)
(* Stage 1: State-relation definitions and equivalences with           *)
(*          preserves / preserves_when instances.                      *)
(* ================================================================== *)

(* rollback_rel: the entire rollback state is unchanged. *)
Definition rollback_rel_def:
  rollback_rel s s' ⇔ s'.rollback = s.rollback
End

(* storage_rel: storage at every address and key is unchanged. *)
Definition storage_rel_def:
  storage_rel s s' ⇔
    ∀a k.
      lookup_storage k (lookup_account a s'.rollback.accounts).storage =
      lookup_storage k (lookup_account a s.rollback.accounts).storage
End

(* access_monotone_sk_rel: storageKeys only grow (subset). *)
Definition access_monotone_sk_rel_def:
  access_monotone_sk_rel s s' ⇔
    toSet s.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys
End

(* access_monotone_addr_rel: addresses only grow (subset). *)
Definition access_monotone_addr_rel_def:
  access_monotone_addr_rel s s' ⇔
    toSet s.rollback.accesses.addresses ⊆
      toSet s'.rollback.accesses.addresses
End

(* pns_rel: storage at (a,k) is preserved unless (SK a k) is
   in the final storageKeys. This is the relation underlying pns. *)
Definition pns_rel_def:
  pns_rel s s' ⇔
    ∀a k.
      ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
      lookup_storage k (lookup_account a s'.rollback.accounts).storage =
      lookup_storage k (lookup_account a s.rollback.accounts).storage
End

Theorem preserves_rollback_eq_preserves:
  preserves_rollback m ⇔ preserves rollback_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_eq_preserves:
  preserves_storage m ⇔ preserves storage_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_monotone_eq_preserves:
  access_monotone m ⇔ preserves access_monotone_sk_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pns_eq_preserves:
  pns m ⇔ preserves pns_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================== *)
(* Reflexivity and transitivity of state relations.                    *)
(*                                                                    *)
(* These are needed as side-conditions for the generic composition   *)
(* lemmas preserves_bind / preserves_when_bind. Each is trivially     *)
(* proved from the relation definition.                               *)
(* ================================================================== *)

Theorem rollback_rel_refl:
  ∀s. rollback_rel s s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem rollback_rel_trans:
  rollback_rel s1 s2 ∧ rollback_rel s2 s3 ⇒ rollback_rel s1 s3
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem storage_rel_refl:
  ∀s. storage_rel s s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem storage_rel_trans:
  storage_rel s1 s2 ∧ storage_rel s2 s3 ⇒ storage_rel s1 s3
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_monotone_sk_rel_refl:
  ∀s. access_monotone_sk_rel s s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_monotone_sk_rel_trans:
  access_monotone_sk_rel s1 s2 ∧ access_monotone_sk_rel s2 s3 ⇒
  access_monotone_sk_rel s1 s3
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_monotone_addr_rel_refl:
  ∀s. access_monotone_addr_rel s s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_monotone_addr_rel_trans:
  access_monotone_addr_rel s1 s2 ∧ access_monotone_addr_rel s2 s3 ⇒
  access_monotone_addr_rel s1 s3
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pns_rel_refl:
  ∀s. pns_rel s s
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================== *)
(* Stage 2: Implication bridges between state relations.               *)
(*                                                                    *)
(* These give bridges between the corresponding predicates for free    *)
(* via preserves_mono.                                                *)
(*                                                                    *)
(* Hierarchy: rollback_rel ⇒ storage_rel ⇒ pns_rel                     *)
(*            rollback_rel ⇒ access_monotone_sk_rel (vacuously, since  *)
(*              rollback_rel means storageKeys is unchanged, thus ⊆)    *)
(* ================================================================== *)

Theorem rollback_rel_imp_storage_rel:
  rollback_rel s s' ⇒ storage_rel s s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem storage_rel_imp_pns_rel:
  storage_rel s s' ⇒ pns_rel s s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem rollback_rel_imp_pns_rel:
  rollback_rel s s' ⇒ pns_rel s s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem rollback_rel_imp_access_monotone_sk_rel:
  rollback_rel s s' ⇒ access_monotone_sk_rel s s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem rollback_rel_imp_access_monotone_addr_rel:
  rollback_rel s s' ⇒ access_monotone_addr_rel s s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* Bridge from same_frame_rel to access_monotone relations.            *)
(* same_frame_rel includes monotone subset constraints on both        *)
(* addresses and storageKeys.                                         *)
Theorem same_frame_rel_imp_access_monotone_sk_rel:
  same_frame_rel s s' ⇒ access_monotone_sk_rel s s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_rel_imp_access_monotone_addr_rel:
  same_frame_rel s s' ⇒ access_monotone_addr_rel s s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived predicate bridges via preserves_mono.                       *)
(* These restate the existing implication theorems                     *)
(* (preserves_rollback_imp_preserves_storage,                        *)
(*  pns_of_preserves_storage,                                          *)
(*  preserves_rollback_imp_pns) in the generic framework.              *)

Theorem preserves_rollback_imp_preserves_storage_via_mono:
  preserves rollback_rel m ⇒ preserves storage_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_imp_pns_via_mono:
  preserves storage_rel m ⇒ preserves pns_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_imp_pns_via_mono:
  preserves rollback_rel m ⇒ preserves pns_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_imp_access_monotone_via_mono:
  preserves rollback_rel m ⇒ preserves access_monotone_sk_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_rel_imp_access_monotone_via_mono:
  preserves same_frame_rel m ⇒ preserves access_monotone_sk_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================== *)
(* Bridges from cp_rel to storage predicates.                         *)
(*                                                                    *)
(* These live here (not in vfmStaticCalls) because they reference     *)
(* storage_rel, pns_rel — defined in this theory.                     *)
(*                                                                    *)
(* IMPORTANT: cp_rel does NOT imply rollback_rel or                   *)
(* access_monotone_sk_rel. cp preserves rollback.accounts/tStorage/    *)
(* toDelete but says nothing about rollback.accesses — operations    *)
(* like access_address, access_slot modify accesses while being cp.   *)
(* Similarly cp and access_monotone are orthogonal properties.         *)
(* ================================================================== *)

(* cp_rel ⇒ storage_rel: accounts preserved ⇒ storage at every       *)
(* (a,k) is preserved.                                                *)
Theorem cp_rel_imp_storage_rel:
  cp_rel s s' ⇒ storage_rel s s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* cp_rel ⇒ pns_rel: if storage at every (a,k) is preserved, then     *)
(* certainly storage at non-accessed (a,k) is preserved.              *)
Theorem cp_rel_imp_pns_rel:
  cp_rel s s' ⇒ pns_rel s s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* Predicate-level bridges via preserves_mono. *)
Theorem cp_imp_preserves_storage_via_mono:
  preserves cp_rel m ⇒ preserves storage_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_imp_pns_via_mono:
  preserves cp_rel m ⇒ preserves pns_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_bind[simp]:
  preserves_rollback g ∧ (∀x. preserves_rollback (f x)) ⇒
  preserves_rollback (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_ignore_bind[simp]:
  preserves_rollback g ∧ preserves_rollback f ⇒
  preserves_rollback (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_return[simp]:
  preserves_rollback (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_fail[simp]:
  preserves_rollback (fail e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_reraise[simp]:
  preserves_rollback (reraise e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_cond[simp]:
  preserves_rollback m1 ∧ preserves_rollback m2 ⇒
  preserves_rollback (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_current_context[simp]:
  preserves_rollback get_current_context
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_set_current_context[simp]:
  preserves_rollback (set_current_context c)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_static[simp]:
  preserves_rollback get_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_assert[simp]:
  preserves_rollback (assert b e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_pop_stack[simp]:
  preserves_rollback (pop_stack n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_consume_gas[simp]:
  preserves_rollback (consume_gas g)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_expand_memory[simp]:
  preserves_rollback (expand_memory g)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_read_memory[simp]:
  preserves_rollback (read_memory off sz)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_assert_not_static[simp]:
  preserves_rollback assert_not_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_callee[simp]:
  preserves_rollback get_callee
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_push_logs[simp]:
  preserves_rollback (push_logs ls)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_memory_expansion_info[simp]:
  preserves_rollback (memory_expansion_info off sz)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_update_gas_refund[simp]:
  preserves_rollback (update_gas_refund p)
Proof
  cheat  (* SCAFFOLD *)
QED

(* step_inst (Log n) preserves rollback entirely. *)
Theorem step_inst_Log_preserves_rollback:
  preserves_rollback (step_inst (Log n))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_Log_storage_preserved:
  step_inst (Log n) s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_imp_preserves_storage[simp]:
  preserves_rollback m ⇒ preserves_storage m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_bind[simp]:
  preserves_storage g ∧ (∀x. preserves_storage (f x)) ⇒
  preserves_storage (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_ignore_bind[simp]:
  preserves_storage g ∧ preserves_storage f ⇒
  preserves_storage (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_cond[simp]:
  preserves_storage m1 ∧ preserves_storage m2 ⇒
  preserves_storage (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_return[simp]:
  preserves_storage (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_fail[simp]:
  preserves_storage (fail e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_reraise[simp]:
  preserves_storage (reraise e)
Proof
  cheat  (* SCAFFOLD *)
QED

(* transfer_value preserves storage at every address. *)
Theorem preserves_storage_transfer_value[simp]:
  preserves_storage (update_accounts (transfer_value fromAddr toAddr amt))
Proof
  cheat  (* SCAFFOLD *)
QED

(* access_address may modify rollback.accesses (in Collect mode) so
   it's not preserves_rollback, but it preserves storage. *)
Theorem preserves_storage_access_address[simp]:
  preserves_storage (access_address addr)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_accounts[simp]:
  preserves_rollback get_accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_gas_left[simp]:
  preserves_rollback get_gas_left
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_original[simp]:
  preserves_rollback get_original
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_finish[simp]:
  preserves_rollback finish
Proof
  cheat  (* SCAFFOLD *)
QED

(* add_to_delete modifies toDelete only; storage preserved. *)
Theorem preserves_storage_add_to_delete[simp]:
  preserves_storage (add_to_delete addr)
Proof
  cheat  (* SCAFFOLD *)
QED

(* update_account at an address with an account whose storage matches
   the original: storage preserved at every address. *)
Theorem preserves_storage_update_account_same_storage:
  (∀accs. (lookup_account addr (f accs)).storage =
          (lookup_account addr accs).storage) ∧
  (∀accs a. a ≠ addr ⇒ f accs a = accs a) ⇒
  preserves_storage (update_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

(* step_self_destruct: the only update_accounts it performs is
   transfer_value, and preserves_storage_transfer_value covers it. *)

Theorem preserves_storage_step_self_destruct:
  preserves_storage step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

(* All preserves_rollback primitives are preserves_storage. *)
Theorem step_inst_SelfDestruct_storage_preserved:
  step_inst SelfDestruct s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
QED

(* After access_slot x (when it succeeds), x is in storageKeys. *)
Theorem access_slot_adds_to_storageKeys:
  access_slot x s = (INL v, s') ⇒
  fIN x s'.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_monotone_bind[simp]:
  access_monotone g ∧ (∀x. access_monotone (f x)) ⇒
  access_monotone (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_monotone_ignore_bind[simp]:
  access_monotone g ∧ access_monotone f ⇒
  access_monotone (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_monotone_cond[simp]:
  access_monotone m1 ∧ access_monotone m2 ⇒
  access_monotone (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_monotone_of_preserves_rollback[simp]:
  preserves_rollback m ⇒ access_monotone m
Proof
  cheat  (* SCAFFOLD *)
QED

(* access_slot: storageKeys grows (by inserting x). *)
Theorem access_monotone_access_slot[simp]:
  access_monotone (access_slot x)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Once (SK address key) is in storageKeys, any access_monotone
   continuation keeps it there. *)
Theorem access_monotone_preserves_slot_membership:
  access_monotone m ∧ m s = (r, s') ∧
  fIN x s.rollback.accesses.storageKeys ⇒
  fIN x s'.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

(* step_sstore_gas_consumption address key value: whenever it
   runs to completion, (SK address key) ends up in storageKeys.

   Proof: use access_monotone for the whole step (each primitive
   is access_monotone) plus `access_slot_adds_to_storageKeys` at
   the specific access_slot (SK address key) call. *)
Theorem access_monotone_step_sstore_gas_consumption[simp]:
  access_monotone (step_sstore_gas_consumption address key value)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_sstore_gas_consumption_adds_slot:
  step_sstore_gas_consumption address key value s = (INL v, s') ⇒
  fIN (SK address key) s'.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

(* write_storage address key value: the only primitive that writes
   accounts.storage. Modifies storage only at (address, key). *)
Theorem write_storage_effect:
  write_storage address key value s = (INL v, s') ⇒
  ∀a k. (a, k) ≠ (address, key) ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* write_storage preserves accesses.storageKeys (via the lemma above). *)
Theorem write_storage_preserves_storageKeys:
  write_storage address key value s = (r, s') ⇒
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_step_sstore_gas_consumption:
  preserves_storage (step_sstore_gas_consumption address key value)
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* A monadic predicate combining preserves_storage with the
   access-listing invariant: storage at (a,k) unchanged UNLESS
   (SK a k) was added to storageKeys. This is exactly what we want. *)

Theorem pns_of_preserves_storage:
  preserves_storage m ⇒ pns m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pns_bind_preserves_storage:
  preserves_storage g ∧ (∀x. pns (f x)) ⇒ pns (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pns_ignore_bind_preserves_storage:
  preserves_storage g ∧ pns f ⇒ pns (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

(* General pns compositional: all pieces must be pns and access_monotone. *)
Theorem pns_bind_access_monotone:
  pns g ∧ access_monotone g ∧ (∀x. pns (f x)) ∧ (∀x. access_monotone (f x)) ⇒
  pns (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pns_ignore_bind_access_monotone:
  pns g ∧ access_monotone g ∧ pns f ∧ access_monotone f ⇒
  pns (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pns_cond[simp]:
  pns m1 ∧ pns m2 ⇒ pns (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pns_return[simp]:
  pns (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pns_fail[simp]:
  pns (fail e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pns_reraise[simp]:
  pns (reraise e)
Proof
  cheat  (* SCAFFOLD *)
QED

(* preserves_rollback ⇒ access_monotone ∧ pns. *)
Theorem preserves_rollback_imp_pns:
  preserves_rollback m ⇒ pns m
Proof
  cheat  (* SCAFFOLD *)
QED

(* pns handle: if f is pns + access_monotone and every h e is pns +
   access_monotone, then handle f h is pns. *)
Theorem pns_handle:
  pns f ∧ access_monotone f ∧
  (∀e. pns (h e)) ∧ (∀e. access_monotone (h e)) ⇒
  pns (handle f h)
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_SStore_storage_preserved:
  step_inst SStore s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem inc_pc_or_jump_inr_eq:
  inc_pc_or_jump op s = (INR e, s') ⇒
    e IN {SOME InvalidJumpDest; SOME Impossible}
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED


(* access_monotone of step: storageKeys never shrinks. Needed for the
   compositional proof of step_preserves_non_accessed_storage. *)
Theorem access_monotone_same_frame:
  same_frame_rel s s' ⇒
    toSet s.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_output_to[simp]:
  preserves_rollback get_output_to
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_return_data[simp]:
  preserves_rollback get_return_data
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_create preserves storage: it may install code at the callee
   but doesn't touch .storage field. *)
Theorem preserves_storage_handle_create:
  preserves_storage (handle_create e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_set_return_data[simp]:
  preserves_rollback (set_return_data rd)
Proof
  cheat  (* SCAFFOLD *)
QED

(* =====================================================================
 * Additional primitive preserves_rollback / preserves_storage lemmas
 * needed for the call/create same-frame abort-path analysis.
 * ===================================================================== *)

Theorem preserves_rollback_push_stack[simp]:
  preserves_rollback (push_stack w)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_inc_pc[simp]:
  preserves_rollback inc_pc
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_unuse_gas[simp]:
  preserves_rollback (unuse_gas n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_num_contexts[simp]:
  preserves_rollback get_num_contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_value[simp]:
  preserves_rollback get_value
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_caller[simp]:
  preserves_rollback get_caller
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_set_domain[simp]:
  preserves_rollback (set_domain d)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_ensure_storage_in_domain[simp]:
  preserves_rollback (ensure_storage_in_domain a)
Proof
  cheat  (* SCAFFOLD *)
QED

(* set_original modifies the separate original-account map, not the
   outer rollback field. So preserves_rollback holds trivially. *)
Theorem preserves_rollback_set_original[simp]:
  preserves_rollback (set_original a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_get_rollback[simp]:
  preserves_rollback get_rollback
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_abort_call_value[simp]:
  preserves_rollback (abort_call_value stipend)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_abort_unuse[simp]:
  preserves_rollback (abort_unuse n)
Proof
  cheat  (* SCAFFOLD *)
QED

(* update_accounts (increment_nonce a) only modifies .nonce, not .storage. *)
Theorem preserves_storage_update_accounts_increment_nonce[simp]:
  preserves_storage (update_accounts (increment_nonce a))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_abort_create_exists[simp]:
  preserves_storage (abort_create_exists a)
Proof
  cheat  (* SCAFFOLD *)
QED

(* The composed update (transfer_value o increment_nonce) preserves
   storage because neither operation touches .storage. *)
Theorem preserves_storage_update_accounts_transfer_increment_nonce[simp]:
  preserves_storage
    (update_accounts
       (transfer_value sender recipient value o increment_nonce recipient))
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* Each precompile is preserves_rollback. *)
Theorem preserves_rollback_precompile_ecrecover[simp]:
  preserves_rollback precompile_ecrecover
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_identity[simp]:
  preserves_rollback precompile_identity
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_modexp[simp]:
  preserves_rollback precompile_modexp
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_sha2_256[simp]:
  preserves_rollback precompile_sha2_256
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_ripemd_160[simp]:
  preserves_rollback precompile_ripemd_160
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_ecadd[simp]:
  preserves_rollback precompile_ecadd
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_ecmul[simp]:
  preserves_rollback precompile_ecmul
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_ecpairing[simp]:
  preserves_rollback precompile_ecpairing
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_blake2f[simp]:
  preserves_rollback precompile_blake2f
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_point_eval[simp]:
  preserves_rollback precompile_point_eval
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_bls_g1add[simp]:
  preserves_rollback precompile_bls_g1add
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_bls_g1msm[simp]:
  preserves_rollback precompile_bls_g1msm
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_bls_g2add[simp]:
  preserves_rollback precompile_bls_g2add
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_bls_g2msm[simp]:
  preserves_rollback precompile_bls_g2msm
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_bls_pairing[simp]:
  preserves_rollback precompile_bls_pairing
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_bls_map_fp_to_g1[simp]:
  preserves_rollback precompile_bls_map_fp_to_g1
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_bls_map_fp2_to_g2[simp]:
  preserves_rollback precompile_bls_map_fp2_to_g2
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_precompile_p256verify[simp]:
  preserves_rollback precompile_p256verify
Proof
  cheat  (* SCAFFOLD *)
QED

(* Precompiles are all preserves_rollback. *)
Theorem preserves_rollback_dispatch_precompiles[simp]:
  preserves_rollback (dispatch_precompiles a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_push_context[simp]:
  preserves_rollback (push_context crb)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_case_pair[simp]:
  (∀x y. preserves_storage (f x y)) ⇒
  preserves_storage (case p of (x, y) => f x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_UNCURRY[simp]:
  (∀x y. preserves_storage (f x y)) ⇒
  preserves_storage (UNCURRY f p)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_let[simp]:
  (∀x. preserves_storage (f x)) ⇒
  preserves_storage (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_proceed_call[simp]:
  preserves_storage
    (proceed_call op sender address value argsOffset argsSize code stipend outputTo)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_proceed_create[simp]:
  preserves_storage
    (proceed_create senderAddress address value code cappedGas)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_step_call:
  preserves_storage (step_call op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_storage_step_create:
  preserves_storage (step_create two)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_same_frame_preserves_storage:
  step_call op s = (INL (), s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_same_frame_preserves_storage:
  step_create two s = (INL (), s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ∧ s.contexts ≠ [] ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* set_jump_dest preserves rollback *)
Theorem preserves_rollback_set_jump_dest[simp]:
  preserves_rollback (set_jump_dest d)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_step_jump[simp]:
  preserves_rollback step_jump
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_step_jumpi[simp]:
  preserves_rollback step_jumpi
Proof
  cheat  (* SCAFFOLD *)
QED

(* step_inst Jump and step_inst JumpI preserve rollback *)
Theorem step_inst_Jump_preserves_rollback:
  preserves_rollback (step_inst Jump)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_JumpI_preserves_rollback:
  preserves_rollback (step_inst JumpI)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_Stop_preserves_rollback[simp]:
  preserves_rollback (step_inst Stop)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_rollback_revert[simp]:
  preserves_rollback revert
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_return_preserves_rollback[simp]:
  preserves_rollback (step_return b)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_Return_preserves_rollback[simp]:
  preserves_rollback (step_inst Return)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_Revert_preserves_rollback[simp]:
  preserves_rollback (step_inst Revert)
Proof
  cheat  (* SCAFFOLD *)
QED
