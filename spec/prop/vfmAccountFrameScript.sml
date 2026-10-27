(* ==========================================================================
 * Per-account frame for run_call.
 *
 * A step whose current context's callee is not `a` changes account `a` only
 * by a foreign_account_change: its code and storage stay, and its nonce
 * stays unless `a` is not yet created (a CREATE at `a`).  So during run_call
 * `a`'s code and storage change only inside frames executing as `a`.
 *
 * run_call_account_frame is the rely form: if every frame entered as `a`
 * preserves a predicate P of `a`'s account, then run_call preserves P.
 * run_call_empty_code_account instantiates it for an account with no code.
 * ========================================================================== *)
Theory vfmAccountFrame
Ancestors
  combin pair option list rich_list relation arithmetic While
  vfmTypes vfmState vfmContext vfmExecution vfmExecutionProp
  vfmSameFrame vfmRunWithinFrame vfmRunCall vfmStaticCalls vfmDecreasesGas
  vfmStoragePredicates vfmPreserves vfmHandleStep vfmStepLength
Libs
  BasicProvers

(* -------------------------------------------------------------------------
 * What a frame not executing as an account can do to it.
 * ------------------------------------------------------------------------- *)

(* Balance is free (value transfers); the nonce may change only for an
 * account a CREATE may target (EIP-7610: no nonce, code or storage). *)
Definition foreign_account_change_def:
  foreign_account_change acc acc' ⇔
    acc'.code = acc.code ∧ acc'.storage = acc.storage ∧
    (acc'.nonce = acc.nonce ∨ ¬account_already_created acc)
End

Theorem foreign_account_change_refl[simp]:
  foreign_account_change acc acc
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem foreign_account_change_trans:
  foreign_account_change acc1 acc2 ∧ foreign_account_change acc2 acc3 ⇒
  foreign_account_change acc1 acc3
Proof
  cheat  (* SCAFFOLD *)
QED

(* -------------------------------------------------------------------------
 * States run_call es takes a step from or reaches with a continuing result.
 * ------------------------------------------------------------------------- *)

Definition run_call_reaches_def:
  run_call_reaches es s ⇔
    RTC (λs1 s2. LENGTH es.contexts ≤ LENGTH s1.contexts ∧
                 ∃u. step s1 = (INL u, s2)) es s
End

Theorem run_call_reaches_refl[simp]:
  run_call_reaches es es
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_reaches_step:
  run_call_reaches es s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
  step s = (INL u, s') ⇒
  run_call_reaches es s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* An invariant of every step holds at every reached state. *)
Theorem run_call_reaches_inv:
  Q es ∧
  (∀s u s'. Q s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
            step s = (INL u, s') ⇒ Q s') ∧
  run_call_reaches es s ⇒
  Q s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_reaches_wf_state:
  wf_state es ∧ run_call_reaches es s ⇒ wf_state s
Proof
  cheat  (* SCAFFOLD *)
QED

(* OWHILE from any state on its own trajectory gives the same result. *)
Theorem OWHILE_RTC:
  ∀x y. RTC (λx y. G x ∧ f x = y) x y ⇒ OWHILE G f x = OWHILE G f y
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem OWHILE_finite_trace:
  OWHILE G f x = SOME y ⇒
  ∃n. FUNPOW f n x = y ∧ ¬G y ∧
      ∀k. k < n ⇒ G (FUNPOW f k x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem OWHILE_from_finite_trace:
  ∀n x. ¬G (FUNPOW f n x) ∧
    (∀k. k < n ⇒ G (FUNPOW f k x)) ⇒
    OWHILE G f x = SOME (FUNPOW f n x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem OWHILE_nested_trace:
  (∀z. H z ⇒ G z) ∧ ¬G (FUNPOW f n x) ⇒
  ∃m. m ≤ n ∧
      OWHILE H f x = SOME (FUNPOW f m x) ∧
      ¬H (FUNPOW f m x) ∧
      (∀k. k < m ⇒ H (FUNPOW f k x))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_finite_trace:
  run_call es = SOME (r, es') ⇒
  ∃n. FUNPOW (step o SND) n (INL (), es) = (r, es') ∧
      ¬(ISL r ∧ LENGTH es.contexts ≤ LENGTH es'.contexts) ∧
      ∀k. k < n ⇒
        ISL (FST (FUNPOW (step o SND) k (INL (), es))) ∧
        LENGTH es.contexts ≤
          LENGTH (SND (FUNPOW (step o SND) k (INL (), es))).contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_trace_reaches:
  ∀n. (∀k. k < n ⇒
          ISL (FST (FUNPOW (step o SND) k (INL (), es))) ∧
          LENGTH es.contexts ≤
            LENGTH (SND (FUNPOW (step o SND) k (INL (), es))).contexts) ∧
      ISL (FST (FUNPOW (step o SND) n (INL (), es))) ⇒
      run_call_reaches es (SND (FUNPOW (step o SND) n (INL (), es)))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_nested_trace:
  d ≤ LENGTH e.contexts ∧
  ¬(λ(r,s). ISL r ∧ d ≤ LENGTH s.contexts)
      (FUNPOW (step o SND) n (INL (), e)) ⇒
  ∃m. m ≤ n ∧
      run_call e = SOME (FUNPOW (step o SND) m (INL (), e)) ∧
      ¬(λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
        (FUNPOW (step o SND) m (INL (), e)) ∧
      (∀k. k < m ⇒
        (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
          (FUNPOW (step o SND) k (INL (), e)))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem OWHILE_trace_continuation:
  (∀k. k < n ⇒ G (FUNPOW f k x)) ∧ m ≤ n ⇒
  OWHILE G f x = OWHILE G f (FUNPOW f m x)
Proof
  cheat  (* SCAFFOLD *)
QED

(* -------------------------------------------------------------------------
 * Per-step effect on accounts other than the current callee.
 * ------------------------------------------------------------------------- *)

(* Equality of the storage-key projection composes independently of all
 * other rollback fields. *)
Theorem rollback_preserves_storage_keys[local]:
  preserves_rollback m ⇒
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem storage_keys_bind[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) g ∧
  (∀x. preserves (λs t. t.rollback.accesses.storageKeys =
                          s.rollback.accesses.storageKeys) (f x)) ⇒
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem storage_keys_ignore_bind[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) g ∧
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) f ⇒
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_address_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (access_address a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_slot_foreign_storage_key[local]:
  x ≠ SK y k ⇒
  preserves (λs t. fIN (SK y k) t.rollback.accesses.storageKeys ⇒
                   fIN (SK y k) s.rollback.accesses.storageKeys)
            (access_slot x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem update_accounts_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (update_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem storage_keys_copy_to_memory[local]:
  (∀f. src = SOME f ⇒ preserves_rollback f) ⇒
  preserves_rollback (copy_to_memory gas off srcOff sz src)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem storage_keys_readers_rollback[local]:
  preserves_rollback get_tx_params ∧
  preserves_rollback get_current_code ∧
  preserves_rollback (get_code a) ∧
  preserves_rollback (get_return_data_check off sz) ∧
  preserves_rollback (write_memory off bytes)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_plain_storage_keys[local]:
  op ≠ SLoad ∧ op ≠ SStore ∧ op ≠ TLoad ∧ op ≠ TStore ∧
  op ≠ SelfDestruct ∧ ¬is_call op ⇒
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (step_inst op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys)
    (proceed_call op sender address value argsOffset argsSize code stipend outputTo)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys)
    (proceed_create sender address value code cappedGas)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (step_create two)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (step_call op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem add_to_delete_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (add_to_delete a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_self_destruct_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem storage_key_backward_from_eq[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) m ⇒
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem storage_key_backward_bind[local]:
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) g ∧
  (∀x. preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                          fIN z s.rollback.accesses.storageKeys) (f x)) ⇒
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem storage_key_backward_ignore_bind[local]:
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) g ∧
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) f ⇒
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem sstore_gas_foreign_storage_key[local]:
  address ≠ y ⇒
  preserves (λs t. fIN (SK y k) t.rollback.accesses.storageKeys ⇒
                   fIN (SK y k) s.rollback.accesses.storageKeys)
    (step_sstore_gas_consumption address key value)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_sload_foreign_storage_key[local]:
  s.contexts ≠ [] ∧ step_sload transient s = (r,t) ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ∧
  fIN (SK y k) t.rollback.accesses.storageKeys ⇒
  fIN (SK y k) s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_sstore_foreign_storage_key[local]:
  s.contexts ≠ [] ∧ step_sstore transient s = (r,t) ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ∧
  fIN (SK y k) t.rollback.accesses.storageKeys ⇒
  fIN (SK y k) s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_foreign_storage_key[local]:
  s.contexts ≠ [] ∧ step_inst op s = (r,t) ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ∧
  fIN (SK y k) t.rollback.accesses.storageKeys ⇒
  fIN (SK y k) s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inner_foreign_storage_key[local]:
  wf_state s ∧ step_inner s = (r,t) ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ∧
  fIN (SK y k) t.rollback.accesses.storageKeys ⇒
  fIN (SK y k) s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_saved_storage_keys[local]:
  proceed_call op sender address value argsOffset argsSize code stipend
               outputTo s = (r,t) ∧ s.contexts ≠ [] ⇒
  (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_saved_storage_keys[local]:
  proceed_create sender address value code cappedGas s = (r,t) ∧
  s.contexts ≠ [] ⇒
  (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem saved_storage_keys_bind[local]:
  preserves_same_frame g ∧
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) g ∧
  (∀x s r t. f x s = (r,t) ∧ s.contexts ≠ [] ∧
              LENGTH s.contexts < LENGTH t.contexts ⇒
     (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys) ⇒
  ∀s r t. bind g f s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem saved_storage_keys_same_frame[local]:
  preserves_same_frame m ⇒
  ∀s r t. m s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem saved_storage_keys_ignore_bind[local]:
  preserves_same_frame g ∧
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) g ∧
  (∀s r t. f s = (r,t) ∧ s.contexts ≠ [] ∧
            LENGTH s.contexts < LENGTH t.contexts ⇒
     (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys) ⇒
  ∀s r t. ignore_bind g f s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem saved_storage_keys_cond[local]:
  (∀s r t. m1 s = (r,t) ∧ s.contexts ≠ [] ∧
            LENGTH s.contexts < LENGTH t.contexts ⇒
     (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys) ∧
  (∀s r t. m2 s = (r,t) ∧ s.contexts ≠ [] ∧
            LENGTH s.contexts < LENGTH t.contexts ⇒
     (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys) ⇒
  ∀s r t. (if b then m1 else m2) s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_saved_storage_keys[local]:
  ∀s r t. step_call op s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_saved_storage_keys[local]:
  ∀s r t. step_create two s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_saved_storage_keys[local]:
  s.contexts ≠ [] ∧ same_frame_rel s t ⇒
  MAP (λp. (SND p).accesses.storageKeys) t.contexts =
  MAP (λp. (SND p).accesses.storageKeys) s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_saved_storage_keys_shape[local]:
  step_call op s = (r,t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒
  MAP (λp. (SND p).accesses.storageKeys) t.contexts =
    s.rollback.accesses.storageKeys ::
    MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
  LENGTH t.contexts = LENGTH s.contexts + 1
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_saved_storage_keys_shape[local]:
  step_create two s = (r,t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒
  MAP (λp. (SND p).accesses.storageKeys) t.contexts =
    s.rollback.accesses.storageKeys ::
    MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
  LENGTH t.contexts = LENGTH s.contexts + 1
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_saved_storage_keys_grow[local]:
  step_inst op s = (r,t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒
  MAP (λp. (SND p).accesses.storageKeys) t.contexts =
    s.rollback.accesses.storageKeys ::
    MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
  LENGTH t.contexts = LENGTH s.contexts + 1
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_saved_storage_keys[local]:
  m s = (r,t) ∧ s.contexts ≠ [] ∧ preserves_same_frame m ⇒
  MAP (λp. (SND p).accesses.storageKeys) t.contexts =
    MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
  LENGTH t.contexts = LENGTH s.contexts ∧ t.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inner_saved_storage_keys[local]:
  wf_state s ∧ step_inner s = (r,t) ⇒
  (MAP (λp. (SND p).accesses.storageKeys) t.contexts =
     MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
   LENGTH t.contexts = LENGTH s.contexts) ∨
  (MAP (λp. (SND p).accesses.storageKeys) t.contexts =
     s.rollback.accesses.storageKeys ::
     MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
   LENGTH t.contexts = LENGTH s.contexts + 1)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_exception_storage_keys[local]:
  s.contexts ≠ [] ∧ handle_exception e s = (r,t) ⇒
  t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∨
  (LENGTH t.contexts < LENGTH s.contexts ∧
   t.rollback.accesses.storageKeys =
     (SND (HD s.contexts)).accesses.storageKeys)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_step_storage_keys[local]:
  s.contexts ≠ [] ∧ handle_step e s = (r,t) ⇒
  t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∨
  (LENGTH t.contexts < LENGTH s.contexts ∧
   t.rollback.accesses.storageKeys =
     (SND (HD s.contexts)).accesses.storageKeys)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_same_frame_foreign:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts = LENGTH s.contexts ⇒
  TL s'.contexts = TL s.contexts ∧
  SND (HD s'.contexts) = SND (HD s.contexts) ∧
  (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y s'.rollback.accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem call_prefix_refl:
  s.contexts ≠ [] ⇒
  cp_rel s s ∧ s.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem call_prefix_trans:
  (cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) ∧
  (cp_rel t u ∧ u.rollback.accesses.storageKeys = t.rollback.accesses.storageKeys) ⇒
  cp_rel s u ∧ u.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem call_prefix_contexts:
  cp_rel s t ∧ s.contexts ≠ [] ⇒
  t.contexts ≠ [] ∧ LENGTH t.contexts = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem bind_call_prefix_grows_extract:
  (cp_rel s0 s ∧ s.rollback.accesses.storageKeys = s0.rollback.accesses.storageKeys) ∧
  s0.contexts ≠ [] ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) g ∧
  bind g f s = (r,t) ∧ LENGTH s0.contexts < LENGTH t.contexts ⇒
  ∃x u. g s = (INL x,u) ∧
    (cp_rel s0 u ∧ u.rollback.accesses.storageKeys = s0.rollback.accesses.storageKeys) ∧
    f x u = (r,t)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem call_prefix_of_cp_keys:
  cp m ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) m ⇒
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem call_prefix_keys_leaves:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (pop_stack n) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (memory_expansion_info off sz) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (consume_gas gas) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) assert_not_static ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (expand_memory ext) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (set_return_data data)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem call_prefix_keys_access_address:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (access_address a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem call_prefix_keys_getters:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_accounts ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_gas_left ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_callee ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_num_contexts ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem call_prefix_bind:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) g ∧
  (∀x. preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (f x)) ⇒
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem call_prefix_leaves:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (pop_stack n) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (memory_expansion_info off sz) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (consume_gas gas) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) assert_not_static ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (expand_memory ext) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (set_return_data data) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (access_address a) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_accounts ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_gas_left ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_callee ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_num_contexts ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem call_prefix_delegate_code_selection:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys)
    (case get_delegate bytecode of
       NONE => return (bytecode, 0)
     | SOME d => do
         cost <- access_address d;
         return ((lookup_account d accounts).code, cost)
       od)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_reaches_proceed_call:
  step_call op s = (r,s') ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  ∃u sender address value ao az code gas mr.
    cp_rel s u ∧ u.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
    proceed_call op sender address value ao az code gas (Memory mr) u = (r,s') ∧
    sender = (FST (HD s.contexts)).msgParams.callee ∧
    value ≤ (lookup_account sender s.rollback.accounts).balance ∧
    code = (case get_delegate (lookup_account address s.rollback.accounts).code of
      NONE => (lookup_account address s.rollback.accounts).code
    | SOME d => (lookup_account d s.rollback.accounts).code) ∧
    (¬call_has_value op ⇒ value = 0) ∧
    (op = Call ∧ 0 < value ⇒ ¬(FST (HD s.contexts)).msgParams.static)
Proof
  cheat  (* SCAFFOLD *)
QED


Theorem proceed_call_saved_rollback:
  proceed_call op sender address value ao az code gas rd s = (r, s') ∧
  s.contexts ≠ [] ∧ ¬fIN address precompile_addresses ⇒
  SND (HD s'.contexts) = s.rollback ∧
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

(* EIP-7708: the trivial cases of the ETH-transfer log.  A zero transfer
   and a transfer to self emit nothing, which is what makes the CALLCODE,
   delegatecall and zero-value cases of a call fall out of the definition
   without a case analysis of their own. *)
Theorem transfer_log_zero[simp]:
  transfer_log sender recipient 0 = []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem transfer_log_self[simp]:
  transfer_log address address amount = []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_nonprecompile_frame:
  proceed_call op sender address value ao az code gas rd s = (r, s') ∧
  s.contexts ≠ [] ∧ ¬fIN address precompile_addresses ⇒
  ∃static sg t.
    FST (HD s'.contexts) =
      (initial_context (if op = CallCode ∨ op = DelegateCall then sender else address)
        code static rd sg t) with
        logs := transfer_log sender
                  (if op = CallCode ∨ op = DelegateCall then sender else address) value ∧
    s'.rollback.accounts =
      (if op ≠ CallCode ∧ 0 < value then
         transfer_value sender address value s.rollback.accounts
       else s.rollback.accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_nonprecompile_message:
  proceed_call op sender address value ao az code gas rd s = (r, s') ∧
  s.contexts ≠ [] ∧ ¬fIN address precompile_addresses ⇒
  r = INL () ∧ s'.rollback.tStorage = s.rollback.tStorage ∧
  ∃sg tx.
    FST (HD s'.contexts) =
      (initial_context (if op = CallCode ∨ op = DelegateCall then sender else address)
        code (op = StaticCall ∨ (FST (HD s.contexts)).msgParams.static) rd sg tx) with
        logs := transfer_log sender
                  (if op = CallCode ∨ op = DelegateCall then sender else address) value ∧
    tx.from = (if op = DelegateCall then (FST (HD s.contexts)).msgParams.caller else sender) ∧
    tx.value = (if op = DelegateCall then (FST (HD s.contexts)).msgParams.value else value)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem terminal_bind:
  (∀x s. ISR (FST (f x s))) ⇒ ISR (FST (bind g f s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem terminal_ignore_bind:
  (∀s. ISR (FST (f s))) ⇒ ISR (FST (ignore_bind g f s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem dispatch_precompiles_terminal:
  ISR (FST (dispatch_precompiles a s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_inl_nonprecompile:
  proceed_call op sender address value ao az code gas rd s = (INL (), s') ∧
  s.contexts ≠ [] ⇒ ¬fIN address precompile_addresses
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_push_storage_keys:
  step_call op s = (INL (),s') ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  (SND (HD s'.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_push_foreign_accounts:
  step_call op s = (INL (),s') ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  ∀y. foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y s'.rollback.accounts) ∧
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y (SND (HD s'.contexts)).accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem transfer_value_zero[local,simp]:
  transfer_value sender address 0 accounts = accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_push_new_frame:
  step_call op s = (INL (),s') ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH s'.contexts ∧
  (FST (HD s'.contexts)).msgParams.callee ≠
    (FST (HD s.contexts)).msgParams.callee ⇒
  ∃code static sg mr t.
    FST (HD s'.contexts) =
      (initial_context (FST (HD s'.contexts)).msgParams.callee
        code static (Memory mr) sg t) with
        logs := transfer_log (FST (HD s.contexts)).msgParams.callee
                  (FST (HD s'.contexts)).msgParams.callee t.value ∧
    code = (case get_delegate
               (lookup_account (FST (HD s'.contexts)).msgParams.callee
                  s.rollback.accounts).code of
          NONE => (lookup_account (FST (HD s'.contexts)).msgParams.callee
                     s.rollback.accounts).code
        | SOME d => (lookup_account d s.rollback.accounts).code) ∧
    (FST (HD s'.contexts)).msgParams.caller =
      (FST (HD s.contexts)).msgParams.callee ∧
    (FST (HD s'.contexts)).msgParams.value ≤
      (lookup_account (FST (HD s.contexts)).msgParams.callee
         s.rollback.accounts).balance ∧
    s'.rollback.accounts =
      transfer_value (FST (HD s.contexts)).msgParams.callee
        (FST (HD s'.contexts)).msgParams.callee
        (FST (HD s'.contexts)).msgParams.value s.rollback.accounts ∧
    s'.rollback.tStorage = s.rollback.tStorage ∧
    (static ⇒ (SND (HD s'.contexts)).accounts = s'.rollback.accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem create_prefix_keys_leaves:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (read_memory off sz) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (assert b e) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (ensure_storage_in_domain a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem create_prefix_leaves:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (read_memory off sz) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (assert b e) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (ensure_storage_in_domain a)
Proof
  cheat  (* SCAFFOLD *)
QED

val create_peel =
  drule_at (Pat `bind`) bind_call_prefix_grows_extract
  >> simp[call_prefix_leaves, create_prefix_leaves]
  >> disch_then (qspec_then `s` mp_tac) >> simp[]
  >> qpat_x_assum `bind _ _ _ = _` kall_tac
  >> strip_tac >> gvs[];

Theorem step_create_reaches_proceed_create:
  step_create two s = (r,s') ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  ∃u sender address value code gas.
    cp_rel s u ∧ u.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
    proceed_create sender address value code gas u = (r,s') ∧
    sender = (FST (HD s.contexts)).msgParams.callee ∧
    ¬account_already_created (lookup_account address s.rollback.accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_frame_effects:
  proceed_create sender address value code gas s = (r,s') ∧ s.contexts ≠ [] ⇒
  r = INL () ∧
  s'.rollback.accounts =
    transfer_value sender address value (increment_nonce address (increment_nonce sender s.rollback.accounts)) ∧
  (SND (HD s'.contexts)).accounts = increment_nonce sender s.rollback.accounts ∧
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  (SND (HD s'.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  ∃sg t.
    (FST (HD s'.contexts) =
      (initial_context address code F (Code address) sg t) with
        logs := transfer_log sender address value) ∧
    (* EIP-7708: the log's amount is the frame's endowment. *)
    t.value = value
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem create_foreign_account_updates:
  y ≠ sender ∧ ¬account_already_created (lookup_account address accounts) ⇒
  foreign_account_change (lookup_account y accounts)
    (lookup_account y (transfer_value sender address value
      (increment_nonce address (increment_nonce sender accounts)))) ∧
  foreign_account_change (lookup_account y accounts)
    (lookup_account y (increment_nonce sender accounts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_push_foreign_accounts:
  s.contexts ≠ [] ∧ step_create two s = (r,s') ∧
  LENGTH s.contexts < LENGTH s'.contexts ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
  foreign_account_change (lookup_account y s.rollback.accounts)
    (lookup_account y s'.rollback.accounts) ∧
  foreign_account_change (lookup_account y s.rollback.accounts)
    (lookup_account y (SND (HD s'.contexts)).accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_stack_effects:
  proceed_create sender address value code gas s = (r,s') ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts = SUC (LENGTH s.contexts) ∧
  MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
  FRONT (TL (TL s'.contexts)) = FRONT (TL s.contexts) ∧
  (FST (EL 1 s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  (2 ≤ LENGTH s.contexts ⇒ SND (EL 1 s'.contexts) = SND (HD s.contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_push_stack:
  s.contexts ≠ [] ∧ step_create two s = (r,s') ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  ISL r ∧ LENGTH s'.contexts = SUC (LENGTH s.contexts) ∧
  MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
  FRONT (TL (TL s'.contexts)) = FRONT (TL s.contexts) ∧
  (FST (EL 1 s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  (2 ≤ LENGTH s.contexts ⇒ SND (EL 1 s'.contexts) = SND (HD s.contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_push_storage_keys:
  s.contexts ≠ [] ∧ step_create two s = (r,s') ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  (SND (HD s'.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_push_new_frame:
  s.contexts ≠ [] ∧ step_create two s = (r,s') ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  ∃code sg t.
    FST (HD s'.contexts) =
      (initial_context (FST (HD s'.contexts)).msgParams.callee code F
        (Code (FST (HD s'.contexts)).msgParams.callee) sg t) with
        logs := transfer_log (FST (HD s.contexts)).msgParams.callee
                  (FST (HD s'.contexts)).msgParams.callee t.value ∧
    ¬account_already_created
      (lookup_account (FST (HD s'.contexts)).msgParams.callee s.rollback.accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_grow_dispatch:
  wf_state s ∧ step s = (r,s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  r = INL () ∧
  ((∃op. step_call op s = (INL (),s')) ∨
   (∃two. step_create two s = (INL (),s')))
Proof
  cheat  (* SCAFFOLD *)
QED

(* A push copies the stack below, except that CREATE's set_original may
 * change the last saved rollback.  Only the callee's nonce and the created
 * account's nonce change, and the latter only when it is not yet created. *)
Theorem step_push_foreign:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  ISL r ∧
  LENGTH s'.contexts = SUC (LENGTH s.contexts) ∧
  MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
  FRONT (TL (TL s'.contexts)) = FRONT (TL s.contexts) ∧
  (FST (EL 1 s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  (2 ≤ LENGTH s.contexts ⇒ SND (EL 1 s'.contexts) = SND (HD s.contexts)) ∧
  ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y s'.rollback.accounts) ∧
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y (SND (HD s'.contexts)).accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

(* The frame a push enters as a new callee: a CALL or STATICCALL running the
 * target's code (or its EIP-7702 delegate's), or a CREATE at an address
 * that is not yet created. *)
Theorem step_push_new_frame:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ∧
  (FST (HD s'.contexts)).msgParams.callee ≠
    (FST (HD s.contexts)).msgParams.callee ⇒
  ∃code static rd sg t.
    FST (HD s'.contexts) =
      (initial_context (FST (HD s'.contexts)).msgParams.callee
        code static rd sg t) with
        logs := transfer_log (FST (HD s.contexts)).msgParams.callee
                  (FST (HD s'.contexts)).msgParams.callee t.value ∧
    ((∃mr. rd = Memory mr) ∧
     code =
       (case get_delegate
               (lookup_account (FST (HD s'.contexts)).msgParams.callee
                  s.rollback.accounts).code of
          NONE => (lookup_account (FST (HD s'.contexts)).msgParams.callee
                     s.rollback.accounts).code
        | SOME d => (lookup_account d s.rollback.accounts).code) ∧
     (FST (HD s'.contexts)).msgParams.caller =
       (FST (HD s.contexts)).msgParams.callee ∧
     (FST (HD s'.contexts)).msgParams.value ≤
       (lookup_account (FST (HD s.contexts)).msgParams.callee
          s.rollback.accounts).balance ∧
     s'.rollback.accounts =
       transfer_value (FST (HD s.contexts)).msgParams.callee
         (FST (HD s'.contexts)).msgParams.callee
         (FST (HD s'.contexts)).msgParams.value s.rollback.accounts ∧
     s'.rollback.tStorage = s.rollback.tStorage ∨
     rd = Code (FST (HD s'.contexts)).msgParams.callee ∧
     ¬account_already_created
        (lookup_account (FST (HD s'.contexts)).msgParams.callee
           s.rollback.accounts)) ∧
    (static ⇒ (∃mr. rd = Memory mr) ∧
              (SND (HD s'.contexts)).accounts = s'.rollback.accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_create_foreign_accounts:
  handle_create e s = (q,s') ∧ s.contexts ≠ [] ∧ outputTo_consistent s ⇒
  ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
    foreign_account_change (lookup_account y s.rollback.accounts)
      (lookup_account y s'.rollback.accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_step_pop_foreign_boundary:
  s.contexts = (callee,callee_rb)::parent::rest ∧
  outputTo_consistent_ctx callee ∧ handle_step e s = (q,s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ⇒
  ∃new_parent.
    s'.contexts = (new_parent,SND parent)::rest ∧
    new_parent.msgParams = (FST parent).msgParams ∧
    (s'.rollback.accounts = callee_rb.accounts ∨
     ∀y. y ≠ callee.msgParams.callee ⇒
       foreign_account_change (lookup_account y s.rollback.accounts)
         (lookup_account y s'.rollback.accounts))
Proof
  cheat  (* SCAFFOLD *)
QED

(* A pop restores the popped frame's saved rollback (failure) or keeps the
 * current one, where only the popped frame's callee changed (success). *)
Theorem step_pop_foreign:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts < LENGTH s.contexts ⇒
  ∃new_head parent rest.
    s.contexts = HD s.contexts :: parent :: rest ∧
    s'.contexts = (new_head, SND parent) :: rest ∧
    new_head.msgParams = (FST parent).msgParams ∧
    (s'.rollback.accounts = (SND (HD s.contexts)).accounts ∨
     ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
         foreign_account_change (lookup_account y s.rollback.accounts)
                                (lookup_account y s'.rollback.accounts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_bind[local]:
  (∀s. Q s ⇒ Q (SND (g s))) ∧
  (∀x s. Q s ⇒ Q (SND (f x s))) ⇒
  ∀s. Q s ⇒ Q (SND (bind g f s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_ignore_bind[local]:
  (∀s. Q s ⇒ Q (SND (g s))) ∧
  (∀s. Q s ⇒ Q (SND (f s))) ⇒
  ∀s. Q s ⇒ Q (SND (ignore_bind g f s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_static_guard[local]:
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (ignore_bind assert_not_static f s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_conditional_guard[local]:
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ∧
  (¬b ⇒ ∀s. Q s ⇒ Q (SND (f s))) ⇒
  ∀s. Q s ⇒
    Q (SND (ignore_bind (if b then assert_not_static else return ()) f s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_preserves_static_prefix[local]:
  cp m ⇒ ∀s.
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ⇒
  (0 < n ∧ n ≤ LENGTH (SND (m s)).contexts ∧
   (SND (m s)).rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (m s)).contexts - n + 1) (SND (m s)).contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_preserves_static_prefix[local]:
  value = 0 ∨ op = CallCode ⇒ ∀s.
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ⇒
  (0 < n ∧
   n ≤ LENGTH (SND (proceed_call op sender address value argsOff argsSize code stipend (Memory mr) s)).contexts ∧
   (SND (proceed_call op sender address value argsOff argsSize code stipend (Memory mr) s)).rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (proceed_call op sender address value argsOff argsSize code stipend (Memory mr) s)).contexts - n + 1)
       (SND (proceed_call op sender address value argsOff argsSize code stipend (Memory mr) s)).contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_cp[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ []) ∧ cp m ⇒
  ∀s. Q s ⇒ Q (SND (m s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_bind_cp[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ []) ∧ cp g ∧
  (∀x s. Q s ⇒ Q (SND (f x s))) ⇒
  ∀s. Q s ⇒ Q (SND (bind g f s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_ignore_bind_cp[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ []) ∧ cp g ∧
  (∀s. Q s ⇒ Q (SND (f s))) ⇒
  ∀s. Q s ⇒ Q (SND (ignore_bind g f s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_step_call[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ∧
  (∀op sender address value ao az code stipend mr.
    value = 0 ∨ op = CallCode ⇒
    ∀s. Q s ⇒ Q (SND (proceed_call op sender address value ao az code stipend (Memory mr) s))) ⇒
  ∀s. Q s ⇒ Q (SND (step_call op s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem static_prefix_cp_rel[local]:
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ∧ cp_rel s s' ⇒
  (0 < n ∧ n ≤ LENGTH s'.contexts ∧ s'.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s'.contexts - n + 1) s'.contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem static_prefix_head[local]:
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ⇒
  s.contexts ≠ [] ∧ (FST (HD s.contexts)).msgParams.static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_preserves_static_prefix[local]:
  ∀s.
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ⇒
  (0 < n ∧ n ≤ LENGTH (SND (step_call op s)).contexts ∧
   (SND (step_call op s)).rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (step_call op s)).contexts - n + 1)
       (SND (step_call op s)).contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_sstore[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_sstore transient s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_log[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_log num s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_self_destruct[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_self_destruct s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_create[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_create two s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_step_inst[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ∧
  (∀op s. Q s ⇒ Q (SND (step_call op s))) ⇒
  ∀s. Q s ⇒ Q (SND (step_inst op s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_preserves_static_prefix[local]:
  ∀s.
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ⇒
  (0 < n ∧ n ≤ LENGTH (SND (step_inst op s)).contexts ∧
   (SND (step_inst op s)).rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (step_inst op s)).contexts - n + 1)
       (SND (step_inst op s)).contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem account_prefix_inner[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ []) ∧
  (∀op s. Q s ⇒ Q (SND (step_inst op s))) ⇒
  ∀s. Q s ⇒ Q (SND ((do
    ctxt <- get_current_context;
    case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
    | SOME op => do step_inst op; inc_pc_or_jump op od
    | NONE => if LENGTH ctxt.msgParams.code ≤ ctxt.pc then step_inst Stop
              else step_inst Invalid
  od) s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inner_preserves_static_prefix[local]:
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ∧
  (do
    ctxt <- get_current_context;
    case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
    | SOME op => do step_inst op; inc_pc_or_jump op od
    | NONE => if LENGTH ctxt.msgParams.code ≤ ctxt.pc then step_inst Stop
              else step_inst Invalid
  od) s = (r,s') ⇒
  (0 < n ∧ n ≤ LENGTH s'.contexts ∧ s'.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s'.contexts - n + 1) s'.contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pop_incorporate_account_prefix[local]:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ 1 < LENGTH s.contexts ∧
  s.rollback.accounts = A ∧
  EVERY (λ(c,rb). c.msgParams.static ∧
    (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
    (TAKE (LENGTH s.contexts - n + 1) s.contexts) ⇒
  (SND (pop_and_incorporate_context success s)).rollback.accounts = A ∧
  (n ≤ LENGTH (SND (pop_and_incorporate_context success s)).contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (pop_and_incorporate_context success s)).contexts - n + 1)
       (SND (pop_and_incorporate_context success s)).contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_preserves_account_prefix_exit[local]:
  cp m ∧ s.contexts ≠ [] ∧ s.rollback.accounts = A ∧
  (n ≤ LENGTH s.contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ∧
  m s = (r,s') ⇒
  s'.rollback.accounts = A ∧
  (n ≤ LENGTH s'.contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s'.contexts - n + 1) s'.contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_ex_helper_account_prefix[local]:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
  EVERY (λ(c,rb). c.msgParams.static ∧
    (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
    (TAKE (LENGTH s.contexts - n + 1) s.contexts) ⇒
  (SND (handle_ex_helper e s)).rollback.accounts = A ∧
  (n ≤ LENGTH (SND (handle_ex_helper e s)).contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (handle_ex_helper e s)).contexts - n + 1)
       (SND (handle_ex_helper e s)).contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_exception_account_prefix[local]:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
  EVERY (λ(c,rb). c.msgParams.static ∧
    (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
    (TAKE (LENGTH s.contexts - n + 1) s.contexts) ⇒
  (SND (handle_exception e s)).rollback.accounts = A ∧
  (n ≤ LENGTH (SND (handle_exception e s)).contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (handle_exception e s)).contexts - n + 1)
       (SND (handle_exception e s)).contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_step_account_prefix[local]:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
  EVERY (λ(c,rb). c.msgParams.static ∧
    (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
    (TAKE (LENGTH s.contexts - n + 1) s.contexts) ⇒
  (SND (handle_step e s)).rollback.accounts = A ∧
  (n ≤ LENGTH (SND (handle_step e s)).contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (handle_step e s)).contexts - n + 1)
       (SND (handle_step e s)).contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_preserves_static_account_prefix[local]:
  wf_state s ∧ 0 < n ∧ n ≤ LENGTH s.contexts ∧
  s.rollback.accounts = A ∧
  EVERY (λ(c,rb). c.msgParams.static ∧
    (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
    (TAKE (LENGTH s.contexts - n + 1) s.contexts) ∧
  step s = (r,s') ⇒
  wf_state s' ∧ s'.rollback.accounts = A ∧
  (n ≤ LENGTH s'.contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s'.contexts - n + 1) s'.contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

(* A static frame changes no account: SSTORE, CREATE, SELFDESTRUCT and
 * value-carrying CALL fail in it, and the frames it calls are static too.
 * Its saved rollback must agree on accounts, since a failure restores it. *)
Theorem run_call_static_frame:
  wf_state e ∧
  (FST (HD e.contexts)).msgParams.static ∧
  (∀x. (FST (HD e.contexts)).msgParams.outputTo ≠ Code x) ∧
  (SND (HD e.contexts)).accounts = e.rollback.accounts ∧
  run_call e = SOME (r, e') ⇒
  e'.rollback.accounts = e.rollback.accounts
Proof
  cheat  (* SCAFFOLD *)
QED

(* -------------------------------------------------------------------------
 * The rely form.
 *
 * The frame hypothesis covers each frame entered as `a` from outside any
 * frame of `a`: es itself if its callee is `a`, and each push by a reached
 * state whose callee is not `a` (a CALL/STATICCALL to `a` or a CREATE at
 * `a`; see step_push_new_frame).  run_call e runs that frame until it pops
 * (or the run stops), nested calls included.  Static pushed frames are
 * discharged by run_call_static_frame.
 * ------------------------------------------------------------------------- *)

Theorem active_rollbacks_initial:
  Q es.rollback ∧
  (2 ≤ LENGTH es.contexts ⇒ Q (SND (HD es.contexts))) ⇒
  EVERY Q (active_rollbacks (LENGTH es.contexts) es)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem active_rollbacks_same_stack:
  LENGTH t.contexts = LENGTH s.contexts ∧
  TL t.contexts = TL s.contexts ∧
  SND (HD t.contexts) = SND (HD s.contexts) ⇒
  TL (active_rollbacks d t) = TL (active_rollbacks d s)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_same_frame_account_invariant:
  wf_state s ∧ step s = (r,t) ∧
  LENGTH t.contexts = LENGTH s.contexts ∧
  (FST (HD s.contexts)).msgParams.callee ≠ a ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d s) ⇒
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d t)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem active_rollbacks_push_tail:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  FRONT (TL (TL t.contexts)) = FRONT (TL s.contexts) ∧
  (2 ≤ LENGTH s.contexts ⇒ SND (EL 1 t.contexts) = SND (HD s.contexts)) ⇒
  TL (active_rollbacks d t) =
    SND (HD t.contexts) :: TL (active_rollbacks d s)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_push_account_invariant:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  wf_state s ∧ step s = (r,t) ∧
  LENGTH s.contexts < LENGTH t.contexts ∧
  (FST (HD s.contexts)).msgParams.callee ≠ a ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d s) ⇒
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d t)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem active_rollbacks_pop:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  s.contexts = h::parent::rest ∧
  t.contexts = (new_head,SND parent)::rest ∧
  EVERY Q (active_rollbacks d s) ⇒
  Q s.rollback ∧ Q (SND h) ∧ EVERY Q (TL (active_rollbacks d t))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem active_rollbacks_pop_tail:
  0 < d ∧ d ≤ LENGTH t.contexts ∧
  s.contexts = h::parent::rest ∧
  t.contexts = (new_head,SND parent)::rest ⇒
  TL (active_rollbacks d t) = TL (TL (active_rollbacks d s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_pop_account_invariant:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  wf_state s ∧ step s = (r,t) ∧
  LENGTH t.contexts < LENGTH s.contexts ∧
  (FST (HD s.contexts)).msgParams.callee ≠ a ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d s) ⇒
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d t)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_foreign_account_invariant:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  wf_state s ∧ step s = (r,t) ∧
  (FST (HD s.contexts)).msgParams.callee ≠ a ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d s) ⇒
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d t)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_outer_saved_rollbacks:
  0 < d ∧ d ≤ k ∧ k < LENGTH s.contexts ∧
  wf_state s ∧ step s = (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (TL (active_rollbacks d t)) =
  DROP (LENGTH s.contexts - k) (TL (active_rollbacks d s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_outer_saved_rollbacks:
  0 < d ∧ d ≤ k ∧ k < LENGTH e.contexts ∧
  wf_state e ∧ run_call e = SOME (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (TL (active_rollbacks d t)) =
  DROP (LENGTH e.contexts - k) (TL (active_rollbacks d e))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_popped_saved_rollbacks:
  0 < d ∧ d < LENGTH e.contexts ∧
  wf_state e ∧ run_call e = SOME (INL (),t) ⇒
  TL (active_rollbacks d t) = TL (TL (active_rollbacks d e))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_saved_account_invariant:
  0 < d ∧ d < LENGTH e.contexts ∧ wf_state e ∧
  EVERY Q (TL (active_rollbacks d e)) ∧
  Q t.rollback ∧ run_call e = SOME (INL (),t) ⇒
  EVERY Q (active_rollbacks d t)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_outer_msgParams:
  0 < k ∧ k < LENGTH s.contexts ∧ wf_state s ∧ step s = (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (MAP (λp. (FST p).msgParams) t.contexts) =
  DROP (LENGTH s.contexts - k) (MAP (λp. (FST p).msgParams) s.contexts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_outer_msgParams:
  0 < k ∧ k < LENGTH e.contexts ∧ wf_state e ∧ run_call e = SOME (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (MAP (λp. (FST p).msgParams) t.contexts) =
  DROP (LENGTH e.contexts - k) (MAP (λp. (FST p).msgParams) e.contexts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_parent_msgParams:
  2 ≤ LENGTH e.contexts ∧ wf_state e ∧ run_call e = SOME (INL (),t) ⇒
  (FST (HD t.contexts)).msgParams = (FST (EL 1 e.contexts)).msgParams
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_reaches_trans:
  run_call_reaches es e ∧ LENGTH es.contexts ≤ LENGTH e.contexts ∧
  run_call_reaches e t ⇒ run_call_reaches es t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_step_equation:
  step e = (q,t) ⇒
  run_call e =
    OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
      (step o SND) (q,t)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_child_continuation:
  LENGTH e.contexts ≤ LENGTH c.contexts ∧
  run_call c = SOME (q,t) ⇒
  OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
    (step o SND) (INL (),c) =
  OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
    (step o SND) (q,t)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_foreign_trace:
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  (∀s c q t.
     run_call_reaches es s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
     wf_state s ∧ (FST (HD s.contexts)).msgParams.callee ≠ a ∧
     P (lookup_account a s.rollback.accounts) ∧
     step s = (INL (),c) ∧ LENGTH s.contexts < LENGTH c.contexts ∧
     (FST (HD c.contexts)).msgParams.callee = a ∧
     run_call c = SOME (q,t) ⇒ P (lookup_account a t.rollback.accounts)) ⇒
  ∀n e r t.
    ¬(λ(q,s). ISL q ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
       (FUNPOW (step o SND) n (INL (),e)) ∧
    run_call_reaches es e ∧ LENGTH es.contexts ≤ LENGTH e.contexts ∧
    wf_state e ∧ (FST (HD e.contexts)).msgParams.callee ≠ a ∧
    EVERY (λrb. P (lookup_account a rb.accounts))
      (active_rollbacks (LENGTH e.contexts) e) ∧
    run_call e = SOME (r,t) ⇒ P (lookup_account a t.rollback.accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Resume run_call_foreign_trace[continuing]:
  Cases_on `x` >> gvs[]
  >> Cases_on `LENGTH c.contexts < LENGTH e.contexts`
  >- gvs[Once OWHILE_THM]
  >> Cases_on `LENGTH c.contexts = LENGTH e.contexts`
  >- suspend "same_depth"
  >> suspend "push"
QED

Resume run_call_foreign_trace[same_depth]:
  `run_call_reaches es c` by (irule run_call_reaches_step >> metis_tac[])
  >> `(FST (HD c.contexts)).msgParams.callee ≠ a`
       by (drule_all step_same_frame_foreign >> metis_tac[])
  >> `run_call c = SOME (r,t)` by gvs[run_call_def, GREATER_EQ]
  >> qpat_x_assum `∀m. m < SUC j ⇒ _` (qspec_then `j` mp_tac)
  >> simp[] >> disch_then irule
  >> qexists_tac `c` >> qexists_tac `r`
  >> gvs[FUNPOW, combinTheory.o_DEF]
QED

Resume run_call_foreign_trace[push]:
  `LENGTH e.contexts < LENGTH c.contexts` by decide_tac
  >> `run_call_reaches es c` by (irule run_call_reaches_step >> metis_tac[])
  >> qpat_x_assum `¬(λ(q,s). _) _` mp_tac
  >> simp[Once FUNPOW] >> strip_tac
  >> drule_at (Pat `¬ _`) run_call_nested_trace
  >> simp[] >> strip_tac
  >> rename1 `m ≤ j`
  >> Cases_on `FUNPOW (step o SND) m (INL (),c)`
  >> rename1 `run_call c = SOME (q,v)`
  >> `P (lookup_account a v.rollback.accounts)` by
       (Cases_on `(FST (HD c.contexts)).msgParams.callee = a`
        >- (qpat_x_assum `∀s c q t. _` irule >>
            qexistsl_tac [`c`,`q`,`e`] >> simp[])
        >> qpat_x_assum `∀m. m < SUC j ⇒ _` (qspec_then `m` mp_tac)
        >> simp[] >> disch_then irule
        >> qexists_tac `c` >> qexists_tac `q` >> simp[]
        >> irule active_rollbacks_initial
        >> drule_all step_push_foreign >> strip_tac
        >> gvs[active_rollbacks_def] >> metis_tac[])
  >> `OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
        (step o SND) (INL (),c) =
      OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
        (step o SND) (q,v)`
       by (irule run_call_child_continuation >> simp[])
  >> Cases_on `q`
  >- suspend "child_return"
  >> gvs[Once OWHILE_THM]
QED

Resume run_call_foreign_trace[child_return]:
  Cases_on `x` >> gvs[]
  >> drule_all step_push_foreign >> strip_tac
  >> `LENGTH e.contexts ≤ LENGTH v.contexts`
       by (qpat_assum `run_call c = _`
             (mp_then Any mp_tac (Q.INST
               [`d` |-> `LENGTH e.contexts`, `k` |-> `LENGTH e.contexts`]
               (Q.INST [`e` |-> `c`] run_call_outer_saved_rollbacks))) >> simp[])
  >> `LENGTH v.contexts = LENGTH e.contexts` by decide_tac
  >> `wf_state v` by metis_tac[run_call_preserves_wf_state]
  >> `2 ≤ LENGTH c.contexts` by decide_tac
  >> `(FST (HD v.contexts)).msgParams = (FST (HD e.contexts)).msgParams`
       by (drule_all run_call_parent_msgParams >> simp[])
  >> `EVERY (λrb. P (lookup_account a rb.accounts))
        (active_rollbacks (LENGTH e.contexts) v)`
       by (irule run_call_saved_account_invariant >> simp[] >>
           qexists_tac `c` >> simp[] >> gvs[active_rollbacks_def])
  >> `run_call_reaches c v`
       by (`run_call_reaches c (SND (FUNPOW (step o SND) m (INL (),c)))`
             suffices_by gvs[] >>
           irule run_call_trace_reaches >> simp[] >> rpt strip_tac >>
           first_x_assum drule >> pairarg_tac >> simp[])
  >> `run_call_reaches es v` by (irule run_call_reaches_trans >> metis_tac[LESS_EQ_TRANS, LESS_IMP_LESS_OR_EQ])
  >> `run_call v = SOME (r,t)` by gvs[run_call_def, GREATER_EQ]
  >> `FUNPOW (step o SND) j (INL (),c) =
      FUNPOW (step o SND) (j-m) (INL (),v)`
       by (`j = (j-m)+m` by decide_tac >>
           qpat_assum `j = _` (once_rewrite_tac o single) >> simp[FUNPOW_ADD])
  >> qpat_x_assum `∀m. m < SUC j ⇒ _` (qspec_then `j-m` mp_tac)
  >> simp[] >> disch_then irule
  >> qexistsl_tac [`v`,`r`] >> simp[] >> metis_tac[]
QED

Finalise run_call_foreign_trace

Theorem run_call_account_frame:
  wf_state es ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  P (lookup_account a es.rollback.accounts) ∧
  (2 ≤ LENGTH es.contexts ⇒
     P (lookup_account a (SND (HD es.contexts)).accounts)) ∧
  (∀e r e'.
     (FST (HD e.contexts)).msgParams.callee = a ∧
     wf_state e ∧ P (lookup_account a e.rollback.accounts) ∧
     (2 ≤ LENGTH e.contexts ⇒
        P (lookup_account a (SND (HD e.contexts)).accounts)) ∧
     (e = es ∨
      ∃s u. run_call_reaches es s ∧
            LENGTH es.contexts ≤ LENGTH s.contexts ∧
            wf_state s ∧
            (FST (HD s.contexts)).msgParams.callee ≠ a ∧
            P (lookup_account a s.rollback.accounts) ∧
            step s = (INL u, e) ∧
            LENGTH s.contexts < LENGTH e.contexts ∧
            ¬(FST (HD e.contexts)).msgParams.static) ∧
     run_call e = SOME (r, e') ⇒
     P (lookup_account a e'.rollback.accounts)) ∧
  run_call es = SOME (r, es') ⇒
  P (lookup_account a es'.rollback.accounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Resume run_call_account_frame[rely_push]:
  rpt gen_tac >> strip_tac
  >> `wf_state c` by metis_tac[step_preserves_wf_state, SND]
  >> drule_all step_push_foreign >> strip_tac
  >> `P (lookup_account a c.rollback.accounts) ∧
      P (lookup_account a (SND (HD c.contexts)).accounts)` by metis_tac[]
  >> Cases_on `(FST (HD c.contexts)).msgParams.static`
  >- suspend "static_push"
  >> qpat_x_assum `∀e r e'. _` irule
  >> qexistsl_tac [`c`,`q`] >> simp[]
  >> disj2_tac >> qexists_tac `s` >> simp[]
QED

Resume run_call_account_frame[static_push]:
  `(FST (HD c.contexts)).msgParams.callee ≠ (FST (HD s.contexts)).msgParams.callee`
    by simp[]
  >> `t.rollback.accounts = c.rollback.accounts` suffices_by metis_tac[]
  >> qpat_x_assum `∀e r e'. _` kall_tac
  >> qpat_x_assum `∀k. k < n ⇒ _` kall_tac
  >> drule_all step_push_new_frame >> strip_tac
  >> `(FST (HD c.contexts)).msgParams.static = static ∧
      (FST (HD c.contexts)).msgParams.outputTo = rd`
       by (qpat_assum `FST (HD c.contexts) = (initial_context _ _ _ _ _ _) with logs := _`
             (once_rewrite_tac o single) >>
           simp[initial_context_def, initial_msg_params_def])
  >> qpat_x_assum `FST (HD c.contexts) = (initial_context _ _ _ _ _ _) with logs := _` kall_tac
  >> irule run_call_static_frame >> gvs[] >> metis_tac[]
QED

Finalise run_call_account_frame

(* -------------------------------------------------------------------------
 * Accounts with no code.
 * ------------------------------------------------------------------------- *)

Theorem step_empty_code[local]:
  wf_state e ∧ (FST (HD e.contexts)).msgParams.code = [] ⇒
  step e = handle (step_inst Stop) handle_step e
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_exception_success_accounts[local]:
  handle_exception NONE s = (r,s') ⇒
  s'.rollback.accounts = s.rollback.accounts
Proof
  cheat  (* SCAFFOLD *)
QED

(* A frame running empty code stops at once; if the callee has no code, a
 * code deposit leaves it so. *)
Theorem handle_create_empty_identity[local]:
  s.contexts ≠ [] ∧
  wf_context (FST (HD s.contexts)) ∧
  outputTo_consistent_ctx (FST (HD s.contexts)) ∧
  (FST (HD s.contexts)).returnData = [] ∧
  (lookup_account (FST (HD s.contexts)).msgParams.callee
    s.rollback.accounts).code = [] ⇒
  handle_create NONE s = (INR NONE,s)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_empty_code_exit[local]:
  wf_state e ∧ (FST (HD e.contexts)).msgParams.code = [] ∧
  (lookup_account (FST (HD e.contexts)).msgParams.callee
    e.rollback.accounts).code = [] ∧ step e = (r,s) ⇒
  s.rollback.accounts = e.rollback.accounts ∧
  (¬ISL r ∨ LENGTH s.contexts < LENGTH e.contexts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_empty_code_frame:
  wf_state e ∧
  (FST (HD e.contexts)).msgParams.code = [] ∧
  (lookup_account (FST (HD e.contexts)).msgParams.callee
     e.rollback.accounts).code = [] ∧
  run_call e = SOME (r, e') ⇒
  e'.rollback.accounts = e.rollback.accounts
Proof
  cheat  (* SCAFFOLD *)
QED

(* If `a` has no code and a CREATE at `a` would collide (nonzero nonce or
 * nonempty storage), run_call changes neither its code nor its storage. *)
Theorem run_call_empty_code_account:
  wf_state es ∧
  (lookup_account a es.rollback.accounts).code = [] ∧
  account_already_created (lookup_account a es.rollback.accounts) ∧
  (2 ≤ LENGTH es.contexts ⇒
     (lookup_account a (SND (HD es.contexts)).accounts).code = [] ∧
     (lookup_account a (SND (HD es.contexts)).accounts).storage =
       (lookup_account a es.rollback.accounts).storage ∧
     account_already_created
       (lookup_account a (SND (HD es.contexts)).accounts)) ∧
  ((FST (HD es.contexts)).msgParams.callee = a ⇒
     (FST (HD es.contexts)).msgParams.code = []) ∧
  run_call es = SOME (r, es') ⇒
  (lookup_account a es'.rollback.accounts).code = [] ∧
  (lookup_account a es'.rollback.accounts).storage =
    (lookup_account a es.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
QED

Resume run_call_empty_code_account[empty_entry]:
  `(FST (HD e.contexts)).msgParams.callee ≠ (FST (HD s.contexts)).msgParams.callee`
    by metis_tac[]
  >> drule_all step_push_new_frame >> strip_tac >> gvs[]
  >> qpat_assum `FST (HD e.contexts) = (initial_context _ _ _ _ _ _) with logs := _`
       (once_rewrite_tac o single)
  >> simp[initial_context_def, initial_msg_params_def,
          get_delegate_def, is_delegation_def]
QED

Finalise run_call_empty_code_account

(* -------------------------------------------------------------------------
 * Provenance of storage keys: SK y k enters the access list only in a step
 * executing as y (SLOAD/SSTORE access the callee's slots).
 * ------------------------------------------------------------------------- *)

Theorem step_storage_keys_foreign:
  wf_state s ∧ step s = (r, s') ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ∧
  fIN (SK y k) s'.rollback.accesses.storageKeys ⇒
  fIN (SK y k) s.rollback.accesses.storageKeys ∨
  LENGTH s'.contexts < LENGTH s.contexts ∧
  fIN (SK y k) (SND (HD s.contexts)).accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_push_storage_keys:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  (SND (HD s'.contexts)).accesses.storageKeys =
    s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem active_storage_key_absent_iff[local]:
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys) (active_rollbacks d s) ⇔
  ¬fIN z s.rollback.accesses.storageKeys ∧
  (d ≤ LENGTH s.contexts ⇒
   ∀i. i < LENGTH s.contexts - d + 1 ∧ i + 1 < LENGTH s.contexts ⇒
     ¬fIN z (SND (EL i s.contexts)).accesses.storageKeys)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem active_storage_key_absent_current[local]:
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys) (active_rollbacks d s) ⇒
  ¬fIN z s.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem active_storage_key_absent_head[local]:
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys) (active_rollbacks d s) ∧
  d ≤ LENGTH s.contexts ∧ 2 ≤ LENGTH s.contexts ⇒
  ¬fIN z (SND (HD s.contexts)).accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem active_storage_key_absent_initial[local]:
  wf_state es ∧
  (2 ≤ LENGTH es.contexts ⇒
     ¬fIN z (SND (HD es.contexts)).accesses.storageKeys) ∧
  ¬fIN z es.rollback.accesses.storageKeys ⇒
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys)
        (active_rollbacks (LENGTH es.contexts) es)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem front_eq_el[local]:
  FRONT xs = FRONT ys ∧ i + 1 < LENGTH xs ∧ i + 1 < LENGTH ys ⇒
  EL i xs = EL i ys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_push_saved_key_index[local]:
  wf_state s ∧ step s = (r,t) ∧ LENGTH s.contexts < LENGTH t.contexts ⇒
  ∀i. i + 1 < LENGTH t.contexts ⇒
    (SND (EL i t.contexts)).accesses.storageKeys =
    (if i = 0 then s.rollback.accesses.storageKeys
     else (SND (EL (i-1) s.contexts)).accesses.storageKeys)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem active_storage_key_absent_step[local]:
  wf_state s ∧ 0 < d ∧ d ≤ LENGTH s.contexts ∧ step s = (r,t) ∧
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys) (active_rollbacks d s) ∧
  ¬fIN z t.rollback.accesses.storageKeys ⇒
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys) (active_rollbacks d t)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Every storage key run_call adds for `a` was added by a step executing as
 * `a`, from a reached state. *)
Theorem run_call_storage_key_added:
  wf_state es ∧
  (2 ≤ LENGTH es.contexts ⇒
     ¬fIN (SK a k) (SND (HD es.contexts)).accesses.storageKeys) ∧
  run_call es = SOME (r, es') ∧
  fIN (SK a k) es'.rollback.accesses.storageKeys ∧
  ¬fIN (SK a k) es.rollback.accesses.storageKeys ⇒
  ∃s u s'.
    run_call_reaches es s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
    (FST (HD s.contexts)).msgParams.callee = a ∧
    step s = (u, s') ∧
    ¬fIN (SK a k) s.rollback.accesses.storageKeys ∧
    fIN (SK a k) s'.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED
