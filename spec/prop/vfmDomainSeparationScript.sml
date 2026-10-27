Theory vfmDomainSeparation
Ancestors
  arithmetic combin list pair pred_set finite_set
  vfmState vfmContext vfmExecution vfmExecutionProp
Libs
  BasicProvers

Definition subdomain_def:
  subdomain s1 s2 ⇔
  toSet s1.addresses ⊆ toSet s2.addresses ∧
  toSet s1.storageKeys ⊆ toSet s2.storageKeys ∧
  toSet s1.fullStorages ⊆ toSet s2.fullStorages
End

Theorem subdomain_refl[simp]:
  subdomain d d
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem subdomain_trans:
  subdomain d1 d2 ∧ subdomain d2 d3 ⇒
  subdomain d1 d3
Proof
  cheat  (* SCAFFOLD *)
QED

Definition accounts_agree_modulo_storage_def:
  accounts_agree_modulo_storage addr (a1:evm_accounts) a2 ⇔
  a1 addr = a2 addr with storage := (a1 addr).storage
End

Theorem accounts_agree_modulo_storage_refl[simp]:
  accounts_agree_modulo_storage x a a
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem accounts_agree_modulo_storage_trans:
  accounts_agree_modulo_storage a a1 a2 ∧
  accounts_agree_modulo_storage a a2 a3 ⇒
  accounts_agree_modulo_storage a a1 a3
Proof
  cheat  (* SCAFFOLD *)
QED

Definition rollback_states_agree_modulo_accounts_def:
  rollback_states_agree_modulo_accounts r1 r2 ⇔
  r1 = r2 with accounts := r1.accounts
End

Theorem rollback_states_agree_modulo_accounts_refl[simp]:
  rollback_states_agree_modulo_accounts r r
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem rollback_states_agree_modulo_accounts_trans:
  rollback_states_agree_modulo_accounts r1 r2 ∧
  rollback_states_agree_modulo_accounts r2 r3 ⇒
  rollback_states_agree_modulo_accounts r1 r3
Proof
  cheat  (* SCAFFOLD *)
QED

Definition states_agree_modulo_accounts_def:
  states_agree_modulo_accounts s1 s2 ⇔
  s1.txParams = s2.txParams ∧
  s1.msdomain = s2.msdomain ∧
  rollback_states_agree_modulo_accounts s1.rollback s2.rollback ∧
  MAP FST s1.contexts = MAP FST s2.contexts ∧
  LIST_REL rollback_states_agree_modulo_accounts
    (MAP SND s1.contexts) (MAP SND s2.contexts)
End

Theorem states_agree_modulo_accounts_refl[simp]:
  states_agree_modulo_accounts s s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem states_agree_modulo_accounts_trans:
  states_agree_modulo_accounts s1 s2 ∧
  states_agree_modulo_accounts s2 s3 ⇒
  states_agree_modulo_accounts s1 s3
Proof
  cheat  (* SCAFFOLD *)
QED

(* Domain agreement covers original reads as well as live and saved accounts. *)
Definition domain_accounts_def:
  domain_accounts s =
    s.rollback.accounts :: s.originalAccounts ::
      FRONT (MAP (λcr. (SND cr).accounts) s.contexts)
End

Definition domain_compatible_def:
  domain_compatible s1 s2 ⇔
  states_agree_modulo_accounts s1 s2 ∧
  case s1.msdomain of Enforce d =>
  (∀addr.
       fIN addr d.addresses ⇒
       LIST_REL (accounts_agree_modulo_storage addr)
         (domain_accounts s1) (domain_accounts s2)) ∧
  (∀addr key.
       fIN (SK addr key) d.storageKeys ⇒
       LIST_REL (λa1 a2. (a1 addr).storage key = (a2 addr).storage key)
         (domain_accounts s1) (domain_accounts s2)) ∧
  (∀addr.
       fIN addr d.fullStorages ⇒
       LIST_REL (λa1 a2. (a1 addr).storage = (a2 addr).storage)
         (domain_accounts s1) (domain_accounts s2))
  | _ => T
End

Theorem domain_compatible_refl[simp]:
  domain_compatible x x
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem domain_compatible_trans:
  domain_compatible s1 s2 ∧
  domain_compatible s2 s3 ⇒
  domain_compatible s1 s3
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem domain_compatible_lengths:
  domain_compatible s1 s2 ⇒
  LENGTH s1.contexts = LENGTH s2.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem LIST_REL_domain_accounts:
  LIST_REL R (domain_accounts s) (domain_accounts t) <=>
  R s.rollback.accounts t.rollback.accounts /\
  R s.originalAccounts t.originalAccounts /\
  LIST_REL R (FRONT (MAP (\cr. (SND cr).accounts) s.contexts))
             (FRONT (MAP (\cr. (SND cr).accounts) t.contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem domain_compatible_original_accounts:
  domain_compatible s t /\ s.msdomain = Enforce d /\
  fIN addr d.addresses ==>
  accounts_agree_modulo_storage addr s.originalAccounts t.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem domain_compatible_original_slot:
  domain_compatible s t /\ s.msdomain = Enforce d /\
  fIN (SK addr key) d.storageKeys ==>
  (s.originalAccounts addr).storage key = (t.originalAccounts addr).storage key
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem domain_compatible_original_storage:
  domain_compatible s t /\ s.msdomain = Enforce d /\
  fIN addr d.fullStorages ==>
  (s.originalAccounts addr).storage = (t.originalAccounts addr).storage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem LIST_REL_FRONT_tail:
  LENGTH xs = LENGTH ys /\ LIST_REL R (FRONT xs) (FRONT ys) ==>
  LIST_REL R (FRONT (TL xs)) (FRONT (TL ys))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem domain_compatible_update_original:
  domain_compatible s t ==>
  domain_compatible
    (s with originalAccounts := update_account addr a s.originalAccounts)
    (t with originalAccounts := update_account addr a t.originalAccounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Definition domain_has_callee_def:
  domain_has_callee s ⇔
  ∀c r t d. s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
    c.msgParams.callee ∈ toSet d.addresses
End

Definition preserves_domain_has_callee_def:
  preserves_domain_has_callee p f ⇔
  ∀s r t. p s ∧ domain_has_callee s ∧ f s = (r, t) ⇒
          domain_has_callee t
End

Definition ignores_extra_domain_pred_def:
  ignores_extra_domain_pred p m ⇔
  ∀s r t d1. p s ∧ m s = (r, t) ∧ s.msdomain = Enforce d1 ⇒
    t.msdomain = s.msdomain ∧
    ((∀x. r ≠ INR $ SOME $ OutsideDomain x) ⇒
      ∀d2. subdomain d1 d2 ⇒
        m (s with msdomain := Enforce d2) = (r, t with msdomain := Enforce d2)) ∧
    (∀s'. domain_compatible s s' ⇒
          ∃t'. domain_compatible t t' ∧ m s' = (r, t'))
End

Definition ignores_extra_domain_def:
  ignores_extra_domain (m: α execution) =
  ignores_extra_domain_pred (K T) m
End

val ignores_extra_domain_def =
  SIMP_RULE std_ss [ignores_extra_domain_pred_def]
  ignores_extra_domain_def

Theorem handle_ignores_extra_domain_pred_allow:
  ignores_extra_domain_pred p f ∧
  (∀s. p s ⇒ p (SND (f s))) ∧
  (∀e. if (∃x. e = SOME (OutsideDomain x))
       then (∀s d. s.msdomain = Enforce d ⇒
             ∃t. (g e) s = (INR e, t) ∧
             t.msdomain = s.msdomain ∧
             (∀s'. domain_compatible s s' ⇒
              ∃t'. (g e) s' = (INR e, t') ∧
                    domain_compatible t t'))
       else ignores_extra_domain_pred p (g e))
  ⇒
  ignores_extra_domain_pred p (handle f g)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_ignores_extra_domain:
  ignores_extra_domain f ∧
  (∀s x. FST (f s) ≠ INR (SOME (OutsideDomain x))) ∧
  (∀e. (∀x. e ≠ SOME (OutsideDomain x)) ⇒ ignores_extra_domain (g e))
  ⇒
  ignores_extra_domain (handle f g)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem bind_ignores_extra_domain:
  ignores_extra_domain g ∧
  (∀x. ignores_extra_domain (f x))
  ⇒
  ignores_extra_domain (monad_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ignore_bind_ignores_extra_domain:
  ignores_extra_domain g ∧
  ignores_extra_domain f
  ⇒
  ignores_extra_domain (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ignores_extra_domain_pred_imp:
  ignores_extra_domain f ⇒
  ignores_extra_domain_pred p f
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ignores_extra_domain_imp_pred_bind:
  (∀s s'. p s ⇒ p (SND (g s))) ∧
  ignores_extra_domain g ∧
  (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ignores_extra_domain_imp_pred_pred_bind:
  (∀s s'. p s ⇒ p (SND (g s))) ∧
  ignores_extra_domain_pred p g ∧
  (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem return_ignores_extra_domain[simp]:
  ignores_extra_domain (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

val tac = rpt (
  (irule bind_ignores_extra_domain \\ rw[]) ORELSE
  (irule ignore_bind_ignores_extra_domain \\ rw[])
);

Theorem get_current_context_ignores_extra_domain[simp]:
  ignores_extra_domain get_current_context
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_gas_left_ignores_extra_domain[simp]:
  ignores_extra_domain get_gas_left
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem assert_ignores_extra_domain[simp]:
  ignores_extra_domain (assert e n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_current_context_ignores_extra_domain[simp]:
  ignores_extra_domain (set_current_context c)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem consume_gas_ignores_extra_domain[simp]:
  ignores_extra_domain (consume_gas n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem fail_ignores_extra_domain[simp]:
  ignores_extra_domain (fail x)
Proof
  cheat  (* SCAFFOLD *)
QED

(* EIP-8037: the state gas meter reads and writes the head frame, which
   `domain_compatible` carries along, so it touches no extra domain. *)
Theorem get_state_gas_left_ignores_extra_domain[simp]:
  ignores_extra_domain get_state_gas_left
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem charge_state_gas_ignores_extra_domain[simp]:
  ignores_extra_domain (charge_state_gas n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem credit_state_gas_refund_ignores_extra_domain[simp]:
  ignores_extra_domain (credit_state_gas_refund n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem restore_state_gas_ignores_extra_domain[simp]:
  ignores_extra_domain restore_state_gas
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem commit_state_gas_ignores_extra_domain[simp]:
  ignores_extra_domain commit_state_gas
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem restore_state_gas_to_entry_ignores_extra_domain[simp]:
  ignores_extra_domain (restore_state_gas_to_entry sg)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem repay_state_gas_spill_ignores_extra_domain[simp]:
  ignores_extra_domain repay_state_gas_spill
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem forfeit_remaining_gas_ignores_extra_domain[simp]:
  ignores_extra_domain forfeit_remaining_gas
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem withhold_create_gas_ignores_extra_domain[simp]:
  ignores_extra_domain withhold_create_gas
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem drain_state_gas_reservoir_ignores_extra_domain[simp]:
  ignores_extra_domain drain_state_gas_reservoir
Proof
  cheat  (* SCAFFOLD *)
QED


Theorem set_return_data_ignores_extra_domain[simp]:
  ignores_extra_domain (set_return_data n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem reraise_ignores_extra_domain[simp]:
  ignores_extra_domain (reraise n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inc_pc_ignores_extra_domain[simp]:
  ignores_extra_domain inc_pc
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_output_to_ignores_extra_domain[simp]:
  ignores_extra_domain get_output_to
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_return_data_ignores_extra_domain[simp]:
  ignores_extra_domain get_return_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_num_contexts_ignores_extra_domain[simp]:
  ignores_extra_domain get_num_contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem unuse_gas_ignores_extra_domain[simp]:
  ignores_extra_domain (unuse_gas n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem restore_child_gas_ignores_extra_domain[simp]:
  ignores_extra_domain (restore_child_gas g sr)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem push_logs_ignores_extra_domain[simp]:
  ignores_extra_domain (push_logs n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem push_stack_ignores_extra_domain[simp]:
  ignores_extra_domain (push_stack n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem update_gas_refund_ignores_extra_domain[simp]:
  ignores_extra_domain (update_gas_refund n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem FST_pop_context_ignores_extra_domain:
  (∀x y. FST x = FST y ⇒ f x = f y) ∧
  (∀x. ignores_extra_domain (f x))
  ⇒
  ignores_extra_domain (monad_bind pop_context f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pop_and_incorporate_context_ignores_extra_domain[simp]:
  ignores_extra_domain (pop_and_incorporate_context x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem write_memory_ignores_extra_domain[simp]:
  ignores_extra_domain (write_memory n m)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_exception_ignores_extra_domain[simp]:
  ignores_extra_domain (handle_exception e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_create_ignores_extra_domain[simp]:
  ignores_extra_domain (handle_create e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_step_ignores_extra_domain[simp]:
  ignores_extra_domain (handle_step e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inc_pc_or_jump_ignores_extra_domain[simp]:
  ignores_extra_domain (inc_pc_or_jump x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem finish_ignore_extra_domain[simp]:
  ignores_extra_domain finish
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pop_stack_ignores_extra_domain[simp]:
  ignores_extra_domain (pop_stack n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_binop_ignore_extra_domain[simp]:
  ignores_extra_domain (step_binop x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_modop_ignore_extra_domain[simp]:
  ignores_extra_domain (step_modop x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_monop_ignore_extra_domain[simp]:
  ignores_extra_domain (step_monop x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_context_ignore_extra_domain[simp]:
  ignores_extra_domain (step_context x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_msgParams_ignore_extra_domain[simp]:
  ignores_extra_domain (step_msgParams x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_accounts_ignore_extra_domain_slot_bind:
  (∀x y s d. s.msdomain = Enforce d ∧
    (∀a k. fIN (SK a k) d.storageKeys ⇒
           (x a).storage k = (y a).storage k) ⇒
         f x s = f y s) ∧
  (∀x. ignores_extra_domain (f x))
  ⇒
  ignores_extra_domain (monad_bind get_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_accounts_ignore_extra_domain_pred_bind:
  (∀x y s d. p s ∧ s.msdomain = Enforce d ∧
    (∀a. fIN a d.addresses ⇒ accounts_agree_modulo_storage a x y) ∧
    (∀a. fIN a d.fullStorages ⇒ (x a).storage = (y a).storage)
    ⇒ f x s = f y s) ∧
  (∀s s'. p s ∧ domain_compatible s s' ⇒ p s') ∧
  (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind get_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_accounts_ignore_extra_domain_slot_pred_bind:
  (∀x y s d. p s ∧ s.msdomain = Enforce d ∧
    (∀a k. fIN (SK a k) d.storageKeys ⇒
           (x a).storage k = (y a).storage k) ⇒
         f x s = f y s) ∧
  (∀s s'. p s ∧ domain_compatible s s' ⇒ p s') ∧
  (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind get_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_address_ignore_extra_domain[simp]:
  ignores_extra_domain (access_address x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_slot_ignore_extra_domain[simp]:
  ignores_extra_domain (access_slot x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_address_ignore_extra_domain_bind:
  (∀x. ignores_extra_domain_pred (λs. ∀d. s.msdomain = Enforce d ⇒ a ∈ toSet d.addresses) (f x))
  ⇒
  ignores_extra_domain (monad_bind (access_address a) f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_address_ignore_extra_domain_pred_bind:
  (∀x. ignores_extra_domain_pred
       (λs. q s ∧ ∀d. s.msdomain = Enforce d ⇒ a ∈ toSet d.addresses)
       (f x)) ∧
  (∀s. q s ⇒ q (SND (access_address a s)))
  ⇒
  ignores_extra_domain_pred q (monad_bind (access_address a) f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_slot_ignore_extra_domain_bind:
  (∀x. ignores_extra_domain_pred
         (λs. ∀d. s.msdomain = Enforce d ⇒ a ∈ toSet d.storageKeys)
         (f x))
  ⇒
  ignores_extra_domain (monad_bind (access_slot a) f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_balance_ignore_extra_domain[simp]:
  ignores_extra_domain step_balance
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_exp_ignore_extra_domain[simp]:
  ignores_extra_domain step_exp
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem expand_memory_ignores_extra_domain[simp]:
  ignores_extra_domain (expand_memory z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem read_memory_ignores_extra_domain[simp]:
  ignores_extra_domain (read_memory y z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem memory_expansion_info_ignores_extra_domain[simp]:
  ignores_extra_domain (memory_expansion_info y z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_keccak256_ignore_extra_domain[simp]:
  ignores_extra_domain step_keccak256
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem copy_to_memory_ignore_extra_domain[simp]:
  (∀f. z = SOME f ⇒ ignores_extra_domain f) ⇒
  ignores_extra_domain (copy_to_memory a b x y z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_copy_to_memory_ignore_extra_domain[simp]:
  (∀f. y = SOME f ⇒ ignores_extra_domain f) ⇒
  ignores_extra_domain (step_copy_to_memory x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_call_data_ignores_extra_domain[simp]:
  ignores_extra_domain (get_call_data )
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_data_load_ignore_extra_domain[simp]:
  ignores_extra_domain step_call_data_load
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_ext_code_size_ignore_extra_domain[simp]:
  ignores_extra_domain step_ext_code_size
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_ext_code_hash_ignore_extra_domain[simp]:
  ignores_extra_domain step_ext_code_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_code_ignores_extra_domain:
  ignores_extra_domain_pred (λs. ∀d. s.msdomain = Enforce d ⇒ x ∈ toSet d.addresses) (get_code x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_memory_expansion_info[simp]:
  SND (memory_expansion_info x y s) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_consume_gas_msdomain[simp]:
  (SND (consume_gas n s)).msdomain = s.msdomain
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_ext_code_copy_ignore_extra_domain[simp]:
  ignores_extra_domain step_ext_code_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_tx_params_ignores_extra_domain[simp]:
  ignores_extra_domain get_tx_params
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_txParams_ignores_extra_domain[simp]:
  ignores_extra_domain (step_txParams x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_return_data_check_ignores_extra_domain[simp]:
  ignores_extra_domain (get_return_data_check x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_return_data_copy_ignore_extra_domain[simp]:
  ignores_extra_domain step_return_data_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_block_hash_ignore_extra_domain[simp]:
  ignores_extra_domain step_block_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_blob_hash_ignore_extra_domain[simp]:
  ignores_extra_domain step_blob_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_callee_ignores_extra_domain[simp]:
  ignores_extra_domain get_callee
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_self_balance_ignore_extra_domain:
  ignores_extra_domain_pred (λs.
    ∀c r t d. s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
    c.msgParams.callee ∈ toSet d.addresses)
  step_self_balance
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_pop_ignores_extra_domain[simp]:
  ignores_extra_domain step_pop
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_mload_ignores_extra_domain[simp]:
  ignores_extra_domain step_mload
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_mstore_ignores_extra_domain[simp]:
  ignores_extra_domain (step_mstore x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_tStorage_ignores_extra_domain[simp]:
  ignores_extra_domain get_tStorage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_sload_ignores_extra_domain[simp]:
  ignores_extra_domain (step_sload x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_jump_dest_ignores_extra_domain[simp]:
  ignores_extra_domain (set_jump_dest i)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_jump_ignores_extra_domain[simp]:
  ignores_extra_domain step_jump
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_jumpi_ignores_extra_domain[simp]:
  ignores_extra_domain step_jumpi
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_push_ignores_extra_domain[simp]:
  ignores_extra_domain (step_push x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_dup_ignores_extra_domain[simp]:
  ignores_extra_domain (step_dup x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_static_ignores_extra_domain[simp]:
  ignores_extra_domain get_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem assert_not_static_ignores_extra_domain[simp]:
  ignores_extra_domain assert_not_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_log_ignores_extra_domain[simp]:
  ignores_extra_domain (step_log x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_swap_ignores_extra_domain[simp]:
  ignores_extra_domain (step_swap n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_dupn_ignores_extra_domain[simp]:
  ignores_extra_domain step_dupn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_swapn_ignores_extra_domain[simp]:
  ignores_extra_domain step_swapn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_exchange_ignores_extra_domain[simp]:
  ignores_extra_domain step_exchange
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem revert_ignores_extra_domain[simp]:
  ignores_extra_domain revert
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_return_ignores_extra_domain[simp]:
  ignores_extra_domain (step_return n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_current_code_ignores_extra_domain[simp]:
  ignores_extra_domain get_current_code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_tStorage_ignores_extra_domain[simp]:
  ignores_extra_domain (set_tStorage z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem write_transient_storage_ignores_extra_domain[simp]:
  ignores_extra_domain (write_transient_storage x y z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_original_ignores_extra_domain_pred_bind:
  (∀x y s d.
      p s ∧ s.msdomain = Enforce d ∧
      (∀a.
         fIN a d.addresses ⇒
         accounts_agree_modulo_storage a x y) ⇒
      f x s = f y s) ∧ (∀s s'. p s ∧ domain_compatible s s' ⇒ p s') ∧
   (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind get_original f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_original_ignores_extra_domain_pred_slot_bind:
  (∀x y s d.
      p s ∧ s.msdomain = Enforce d ∧
      (∀a k.
         fIN (SK a k) d.storageKeys ⇒
         (x a).storage k = (y a).storage k) ⇒
      f x s = f y s) ∧ (∀s s'. p s ∧ domain_compatible s s' ⇒ p s') ∧
   (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind get_original f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_original_ignores_extra_domain_slot_bind:
   (∀x y s d. s.msdomain = Enforce d ∧
      (∀a k.
         fIN (SK a k) d.storageKeys ⇒
         (x a).storage k = (y a).storage k) ⇒
      f x s = f y s) ∧ (∀x. ignores_extra_domain (f x)) ⇒
   ignores_extra_domain (monad_bind get_original f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_sstore_gas_consumption_ignores_extra_domain[simp]:
  ignores_extra_domain (step_sstore_gas_consumption z y x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem write_storage_ignores_extra_domain[simp]:
  ignores_extra_domain (write_storage x y z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_sstore_ignores_extra_domain[simp]:
  ignores_extra_domain (step_sstore x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem add_to_delete_ignores_extra_domain[simp]:
  ignores_extra_domain (add_to_delete _)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_callee_ignores_extra_domain_pred_bind:
  (∀x. ignores_extra_domain_pred (λs. p s ∧ (∃c r t. s.contexts = (c,r)::t ∧
                                                     c.msgParams.callee = x))
        (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind get_callee f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ignores_extra_domain_update_accounts_transfer_value[simp]:
  ignores_extra_domain (update_accounts (transfer_value x y z))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ignores_extra_domain_update_accounts_increment_nonce[simp]:
  ignores_extra_domain (update_accounts (increment_nonce a))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_self_destruct_ignores_extra_domain[simp]:
  ignores_extra_domain_pred (λs.
    ∀c r t d. s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
    c.msgParams.callee ∈ toSet d.addresses)
  step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem abort_unuse_ignores_extra_domain[simp]:
  ignores_extra_domain (abort_unuse x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem abort_call_value_ignores_extra_domain[simp]:
  ignores_extra_domain (abort_call_value x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem abort_create_exists_ignores_extra_domain[simp]:
  ignores_extra_domain (abort_create_exists x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_caller_ignores_extra_domain[simp]:
  ignores_extra_domain get_caller
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_value_ignores_extra_domain[simp]:
  ignores_extra_domain get_value
Proof
  cheat  (* SCAFFOLD *)
QED


Theorem precompile_ecrecover_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ecrecover
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_ripemd_160_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ripemd_160
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_sha2_256_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_sha2_256
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_identity_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_identity
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_modexp_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_modexp
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_ecadd_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ecadd
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_ecmul_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ecmul
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_ecpairing_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ecpairing
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_point_eval_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_point_eval
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_blake2f_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_blake2f
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_bls_g1add_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_g1add
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_bls_g1msm_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_g1msm
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_bls_g2add_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_g2add
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_bls_g2msm_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_g2msm
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_bls_pairing_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_pairing
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_bls_map_fp_to_g1_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_map_fp_to_g1
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_bls_map_fp2_to_g2_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_map_fp2_to_g2
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompile_p256verify_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_p256verify
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem dispatch_precompiles_ignores_extra_domain[simp]:
  ignores_extra_domain (dispatch_precompiles x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ignores_extra_domain_update_accounts_nonce[simp]:
  ignores_extra_domain
    (update_accounts (update_account a (b with nonce updated_by f)))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ignores_extra_domain_update_accounts_o[simp]:
  ignores_extra_domain (update_accounts f) ∧
  ignores_extra_domain (update_accounts g)
  ⇒
  ignores_extra_domain (update_accounts (g o f))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_rollback_ignores_extra_domain_bind:
  (∀x y s d.
    rollback_states_agree_modulo_accounts x y ∧
    s.msdomain = Enforce d ∧
           (∀a. a ∈ toSet d.addresses ⇒
                accounts_agree_modulo_storage a x.accounts y.accounts) ∧
           (∀a k. SK a k ∈ toSet d.storageKeys ⇒
                (x.accounts a).storage k = (y.accounts a).storage k) ∧
           (∀a. a ∈ toSet d.fullStorages ⇒
                (x.accounts a).storage = (y.accounts a).storage)
    ⇒
    FST (f x s) = FST (f y s) ∧
    domain_compatible (SND (f x s)) (SND (f y s))) ∧
  (∀x. ignores_extra_domain (f x))
  ⇒
  ignores_extra_domain (monad_bind get_rollback f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem push_context_ignores_extra_domain[simp]:
  ignores_extra_domain (push_context c)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem FST_bind_eq:
  (∀x s'. f s = (INL x, s') ⇒ FST (g1 x s') = FST (g2 x s'))
  ⇒
  FST (monad_bind f g1 s) = FST (monad_bind f g2 s)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem bind_eq:
  (∀x s'. f s = (INL x, s') ⇒ (g1 x s') = (g2 x s'))
  ⇒
  (monad_bind f g1 s) = (monad_bind f g2 s)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_bind_domain_compatible:
  (∀x s'. f s = (INL x, s') ⇒ domain_compatible (SND (g1 x s')) (SND (g2 x s')))
  ⇒
  domain_compatible (SND (monad_bind f g1 s)) (SND (monad_bind f g2 s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_ignores_extra_domain[simp]:
  ignores_extra_domain (proceed_call a b c d e f g h i)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_update_accounts_msdomain[simp]:
  (SND (update_accounts f s)).msdomain = s.msdomain
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_original_set_original_ignores_extra_domain:
  ignores_extra_domain f ⇒
  ignores_extra_domain
    (do original <- get_original;
        set_original (update_account addr a original);
        f od)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_ignores_extra_domain[simp]:
  ignores_extra_domain (proceed_create a b c d e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_ignores_extra_domain:
  ignores_extra_domain_pred
  (λs. ∀c r t d.
    s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
    c.msgParams.callee ∈ toSet d.addresses)
  (step_call x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ensure_storage_in_domain_ignores_extra_domain[simp]:
  ignores_extra_domain (ensure_storage_in_domain a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_ignores_extra_domain:
  ignores_extra_domain_pred
  (λs. ∀c r t d.
    s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
    c.msgParams.callee ∈ toSet d.addresses)
  (step_create x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_ignores_extra_domain:
  ignores_extra_domain_pred
  (λs. ∀c r t d. s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
       c.msgParams.callee ∈ toSet d.addresses)
  (step_inst op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_bind:
  preserves_domain_has_callee p g ∧
  (∀s. p s ⇒ p (SND (g s))) ∧
  (∀x. preserves_domain_has_callee p (f x))
  ⇒
  preserves_domain_has_callee p (monad_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_ignore_bind:
  preserves_domain_has_callee p g ∧
  (∀s. p s ⇒ p (SND (g s))) ∧
  preserves_domain_has_callee p f
  ⇒
  preserves_domain_has_callee p (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_current_context_bind:
  (∀x. preserves_domain_has_callee
       (λs. p s ∧ ∀d. s.msdomain = Enforce d ⇒ x.msgParams.callee ∈ toSet d.addresses)
       (f x))
  ⇒
  preserves_domain_has_callee p (monad_bind get_current_context f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_set_current_context:
  (∀s. p s ⇒ ∀d. s.msdomain = Enforce d ⇒ x.msgParams.callee ∈ toSet d.addresses)
  ⇒
  preserves_domain_has_callee p (set_current_context x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_set_return_data[simp]:
  preserves_domain_has_callee (K T) (set_return_data _)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_finish[simp]:
  preserves_domain_has_callee (K T) (finish)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_assert[simp]:
  preserves_domain_has_callee (K T) (assert b e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_mono:
  preserves_domain_has_callee q f ∧ (∀s. p s ⇒ q s) ⇒
  preserves_domain_has_callee p f
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem assert_msdomain[simp]:
  (SND (assert b e s)).msdomain = s.msdomain
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem return_msdomain[simp]:
  (SND (return x s)).msdomain = s.msdomain
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem fail_msdomain[simp]:
  (SND (fail x s)).msdomain = s.msdomain
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_current_context_msdomain[simp]:
  (SND (set_current_context x s)).msdomain = s.msdomain
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_return[simp]:
  preserves_domain_has_callee (K T) (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_imp[simp]:
  preserves_domain_has_callee (K T) f ⇒
  preserves_domain_has_callee p f
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_pop_stack[simp]:
  preserves_domain_has_callee (K T) (pop_stack n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_consume_gas[simp]:
  preserves_domain_has_callee (K T) (consume_gas n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_push_stack[simp]:
  preserves_domain_has_callee (K T) (push_stack n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_binop[simp]:
  preserves_domain_has_callee (K T) (step_binop x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_modop[simp]:
  preserves_domain_has_callee (K T) (step_modop x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_monop[simp]:
  preserves_domain_has_callee (K T) (step_monop x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_exp[simp]:
  preserves_domain_has_callee (K T) step_exp
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_memory_expansion_info[simp]:
  preserves_domain_has_callee (K T) (memory_expansion_info x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_expand_memory[simp]:
  preserves_domain_has_callee (K T) (expand_memory x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_read_memory[simp]:
  preserves_domain_has_callee (K T) (read_memory x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_keccak256[simp]:
  preserves_domain_has_callee (K T) step_keccak256
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_context[simp]:
  preserves_domain_has_callee (K T) (step_context x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_msgParams[simp]:
  preserves_domain_has_callee (K T) (step_msgParams x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_tx_params[simp]:
  preserves_domain_has_callee (K T) get_tx_params
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_txParams[simp]:
  preserves_domain_has_callee (K T) (step_txParams x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_access_address[simp]:
  preserves_domain_has_callee (K T) (access_address a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_accounts[simp]:
  preserves_domain_has_callee (K T) get_accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_balance[simp]:
  preserves_domain_has_callee (K T) step_balance
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_call_data[simp]:
  preserves_domain_has_callee (K T) get_call_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_call_data_load[simp]:
  preserves_domain_has_callee (K T) step_call_data_load
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_write_memory[simp]:
  preserves_domain_has_callee (K T) (write_memory x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_copy_to_memory[simp]:
  (∀g. f = SOME g ⇒ preserves_domain_has_callee (K T) g)
  ⇒
  preserves_domain_has_callee (K T) (copy_to_memory a b c d f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_copy_to_memory[simp]:
  (∀g. f = SOME g ⇒ preserves_domain_has_callee (K T) g)
  ⇒
  preserves_domain_has_callee (K T) (step_copy_to_memory x f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_current_code[simp]:
  preserves_domain_has_callee (K T) get_current_code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_code[simp]:
  preserves_domain_has_callee (K T) (get_code x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_ext_code_size[simp]:
  preserves_domain_has_callee (K T) step_ext_code_size
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_ext_code_copy[simp]:
  preserves_domain_has_callee (K T) step_ext_code_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_return_data[simp]:
  preserves_domain_has_callee (K T) (get_return_data)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_return_data_check[simp]:
  preserves_domain_has_callee (K T) (get_return_data_check x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_return_data_copy[simp]:
  preserves_domain_has_callee (K T) step_return_data_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_ext_code_hash[simp]:
  preserves_domain_has_callee (K T) step_ext_code_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_block_hash[simp]:
  preserves_domain_has_callee (K T) step_block_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_blob_hash[simp]:
  preserves_domain_has_callee (K T) step_blob_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_callee[simp]:
  preserves_domain_has_callee (K T) get_callee
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_self_balance[simp]:
  preserves_domain_has_callee (K T) step_self_balance
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_pop[simp]:
  preserves_domain_has_callee (K T) step_pop
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_mload[simp]:
  preserves_domain_has_callee (K T) step_mload
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_mstore[simp]:
  preserves_domain_has_callee (K T) (step_mstore x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_access_slot[simp]:
  preserves_domain_has_callee (K T) (access_slot x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_tStorage[simp]:
  preserves_domain_has_callee (K T) get_tStorage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_sload[simp]:
  preserves_domain_has_callee (K T) (step_sload x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_static[simp]:
  preserves_domain_has_callee (K T) get_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_assert_not_static[simp]:
  preserves_domain_has_callee (K T) assert_not_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_set_tStorage[simp]:
  preserves_domain_has_callee (K T) (set_tStorage x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_write_transient_storage[simp]:
  preserves_domain_has_callee (K T) (write_transient_storage x y z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_gas_left[simp]:
  preserves_domain_has_callee (K T) get_gas_left
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_original[simp]:
  preserves_domain_has_callee (K T) get_original
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_update_gas_refund[simp]:
  preserves_domain_has_callee (K T) (update_gas_refund x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_sstore_gas_consumption[simp]:
  preserves_domain_has_callee (K T) (step_sstore_gas_consumption x y z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_update_accounts[simp]:
  preserves_domain_has_callee (K T) (update_accounts f )
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_write_storage[simp]:
  preserves_domain_has_callee (K T) (write_storage x y z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_sstore[simp]:
  preserves_domain_has_callee (K T) (step_sstore x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_set_jump_dest[simp]:
  preserves_domain_has_callee (K T) (set_jump_dest x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_jump[simp]:
  preserves_domain_has_callee (K T) step_jump
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_jumpi[simp]:
  preserves_domain_has_callee (K T) step_jumpi
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_push[simp]:
  preserves_domain_has_callee (K T) (step_push x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_dup[simp]:
  preserves_domain_has_callee (K T) (step_dup y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_swap[simp]:
  preserves_domain_has_callee (K T) (step_swap y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_dupn[simp]:
  preserves_domain_has_callee (K T) step_dupn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_swapn[simp]:
  preserves_domain_has_callee (K T) step_swapn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_exchange[simp]:
  preserves_domain_has_callee (K T) step_exchange
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_push_logs[simp]:
  preserves_domain_has_callee (K T) (push_logs y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_log[simp]:
  preserves_domain_has_callee (K T) (step_log y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_revert[simp]:
  preserves_domain_has_callee (K T) revert
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_return[simp]:
  preserves_domain_has_callee (K T) (step_return _)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_add_to_delete[simp]:
  preserves_domain_has_callee (K T) (add_to_delete x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_self_destruct[simp]:
  preserves_domain_has_callee (K T) step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_unuse_gas[simp]:
  preserves_domain_has_callee (K T) (unuse_gas x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_inc_pc[simp]:
  preserves_domain_has_callee (K T) inc_pc
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_abort_call_value[simp]:
  preserves_domain_has_callee (K T) (abort_call_value x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_num_contexts[simp]:
  preserves_domain_has_callee (K T) get_num_contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_abort_unuse[simp]:
  preserves_domain_has_callee (K T) (abort_unuse x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_rollback[simp]:
  preserves_domain_has_callee (K T) get_rollback
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_get_rollback[simp]:
  SND (get_rollback s) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_get_current_context[simp]:
  SND (get_current_context s) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_read_memory[simp]:
  SND (read_memory x y s) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_get_caller[simp]:
  SND (get_caller s) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_caller[simp]:
  preserves_domain_has_callee (K T) get_caller
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_get_value[simp]:
  SND (get_value s) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_value[simp]:
  preserves_domain_has_callee (K T) get_value
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_get_static[simp]:
  SND (get_static s) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_push_context:
  (∀s. p s ⇒ ∀d. s.msdomain = Enforce d ⇒
      (FST cr).msgParams.callee ∈ toSet d.addresses)
  ⇒
  preserves_domain_has_callee p (push_context cr)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_push_context[simp]:
  SND (push_context cr s) =
  s with contexts updated_by CONS cr
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_fail[simp]:
  preserves_domain_has_callee (K T) (fail x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_precompiles[simp]:
    preserves_domain_has_callee (K T) precompile_ecrecover
  ∧ preserves_domain_has_callee (K T) precompile_sha2_256
  ∧ preserves_domain_has_callee (K T) precompile_ripemd_160
  ∧ preserves_domain_has_callee (K T) precompile_identity
  ∧ preserves_domain_has_callee (K T) precompile_modexp
  ∧ preserves_domain_has_callee (K T) precompile_ecadd
  ∧ preserves_domain_has_callee (K T) precompile_ecmul
  ∧ preserves_domain_has_callee (K T) precompile_ecpairing
  ∧ preserves_domain_has_callee (K T) precompile_blake2f
  ∧ preserves_domain_has_callee (K T) precompile_point_eval
  ∧ preserves_domain_has_callee (K T) precompile_bls_g1add
  ∧ preserves_domain_has_callee (K T) precompile_bls_g1msm
  ∧ preserves_domain_has_callee (K T) precompile_bls_g2add
  ∧ preserves_domain_has_callee (K T) precompile_bls_g2msm
  ∧ preserves_domain_has_callee (K T) precompile_bls_pairing
  ∧ preserves_domain_has_callee (K T) precompile_bls_map_fp_to_g1
  ∧ preserves_domain_has_callee (K T) precompile_bls_map_fp2_to_g2
  ∧ preserves_domain_has_callee (K T) precompile_p256verify
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_dispatch_precompiles[simp]:
  preserves_domain_has_callee (K T) (dispatch_precompiles x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_proceed_call[simp]:
  (∀s d. p s ∧ s.msdomain = Enforce d ⇒
           b ∈ toSet d.addresses ∧
           c ∈ toSet d.addresses) ∧
  (∀s. p s ⇒ ∀x. p (SND (update_accounts x s))) ∧
  (∀s. p s ⇒ ∀cr. (FST cr).msgParams.callee ∈ {b;c} ⇒
                   p (s with contexts updated_by CONS cr))
  ⇒
  preserves_domain_has_callee p (proceed_call a b c d e f g h i)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_access_address_bind:
  (∀x. preserves_domain_has_callee
         (λs. ∀d. s.msdomain = Enforce d ⇒ a ∈ toSet d.addresses ) (f x))
  ⇒
  preserves_domain_has_callee p
    (monad_bind (access_address a) f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_get_accounts[simp]:
  SND (get_accounts s) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_get_gas_left[simp]:
  SND (get_gas_left s) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_assert_not_static[simp]:
  SND (assert_not_static s) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_expand_memory_msdomain[simp]:
  (SND (expand_memory x s)).msdomain = s.msdomain
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_get_callee_bind:
  (∀x. preserves_domain_has_callee (λs. p s ∧ ∀d. s.msdomain = Enforce d ⇒
                                                x ∈ toSet d.addresses)
       (f x))
  ⇒
  preserves_domain_has_callee p (monad_bind get_callee f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_set_return_data_msdomain[simp]:
  (SND (set_return_data x s)).msdomain = s.msdomain
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_get_num_contexts[simp]:
  SND (get_num_contexts s) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_call[simp]:
  preserves_domain_has_callee (K T) (step_call x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_set_original[simp]:
  preserves_domain_has_callee p (set_original a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_proceed_create:
  (∀s d. p s ∧ s.msdomain = Enforce d ⇒ b ∈ toSet d.addresses) ∧
  (∀s. p s ⇒ ∀x. p (SND (update_accounts x s))) ∧
  (∀s. p s ⇒ p (SND (get_original s))) ∧
  (∀s. p s ⇒ ∀a. p (SND (set_original a s))) ∧
  (∀s. p s ⇒ ∀cr. (FST cr).msgParams.callee = b ⇒
                   p (s with contexts updated_by CONS cr))
  ⇒
  preserves_domain_has_callee p (proceed_create a b c d e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_ensure_storage_in_domain[simp]:
  preserves_domain_has_callee (K T) (ensure_storage_in_domain x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_abort_create_exists[simp]:
  preserves_domain_has_callee (K T) (abort_create_exists x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem SND_ensure_storage_in_domain_msdomain_eq_Enforce[simp]:
  ((SND (ensure_storage_in_domain x y)).msdomain = Enforce d) =
  (y.msdomain = Enforce d)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_step_create[simp]:
  preserves_domain_has_callee (K T) (step_create x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_preserves_domain_has_callee[simp]:
  preserves_domain_has_callee (K T) (step_inst op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_domain_has_callee_inc_pc_or_jump[simp]:
  preserves_domain_has_callee (K T) (inc_pc_or_jump x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_ignores_extra_domain_pred:
  ignores_extra_domain_pred
  (λs. ∀c r t d. s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
       c.msgParams.callee ∈ toSet d.addresses)
  step
Proof
  cheat  (* SCAFFOLD *)
QED
