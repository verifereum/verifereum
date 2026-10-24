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
  combin pair option list rich_list relation While
  vfmTypes vfmState vfmContext vfmExecution vfmExecutionProp
  vfmSameFrame vfmRunWithinFrame vfmRunCall vfmStaticCalls vfmPreserves
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
  rw[foreign_account_change_def]
QED

Theorem foreign_account_change_trans:
  foreign_account_change acc1 acc2 ∧ foreign_account_change acc2 acc3 ⇒
  foreign_account_change acc1 acc3
Proof
  rw[foreign_account_change_def] >> gvs[account_already_created_def]
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
  rw[run_call_reaches_def]
QED

Theorem run_call_reaches_step:
  run_call_reaches es s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
  step s = (INL u, s') ⇒
  run_call_reaches es s'
Proof
  rw[run_call_reaches_def]
  >> irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1))
  >> metis_tac[]
QED

(* An invariant of every step holds at every reached state. *)
Theorem run_call_reaches_inv:
  Q es ∧
  (∀s u s'. Q s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
            step s = (INL u, s') ⇒ Q s') ∧
  run_call_reaches es s ⇒
  Q s
Proof
  rw[run_call_reaches_def]
  >> qmatch_asmsub_abbrev_tac `RTC R es s`
  >> `∀x y. RTC R x y ⇒ x = es ⇒ Q y` suffices_by metis_tac[]
  >> ho_match_mp_tac RTC_INDUCT_RIGHT1
  >> rw[Abbr`R`] >> metis_tac[]
QED

Theorem run_call_reaches_wf_state:
  wf_state es ∧ run_call_reaches es s ⇒ wf_state s
Proof
  strip_tac
  >> irule run_call_reaches_inv
  >> qexists_tac `es` >> simp[]
  >> metis_tac[step_preserves_wf_state, SND]
QED

(* OWHILE from any state on its own trajectory gives the same result. *)
Theorem OWHILE_RTC:
  ∀x y. RTC (λx y. G x ∧ f x = y) x y ⇒ OWHILE G f x = OWHILE G f y
Proof
  ho_match_mp_tac RTC_INDUCT
  >> rw[]
  >> simp[Once OWHILE_THM]
QED

(* -------------------------------------------------------------------------
 * Per-step effect on accounts other than the current callee.
 * ------------------------------------------------------------------------- *)

Theorem step_same_frame_foreign:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts = LENGTH s.contexts ⇒
  TL s'.contexts = TL s.contexts ∧
  SND (HD s'.contexts) = SND (HD s.contexts) ∧
  (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y s'.rollback.accounts)
Proof
  strip_tac
  >> `outputTo_consistent s`
       by metis_tac[outputTo_consistent_stack_imp_consistent, wf_state_def]
  >> drule_all step_same_frame
  >> rw[same_frame_rel_def, callee_local_changes_def,
        foreign_account_change_def]
QED

Theorem call_prefix_refl:
  s.contexts ≠ [] ⇒
  cp_rel s s ∧ s.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  simp[cp_rel_refl]
QED

Theorem call_prefix_trans:
  (cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) ∧
  (cp_rel t u ∧ u.rollback.accesses.storageKeys = t.rollback.accesses.storageKeys) ⇒
  cp_rel s u ∧ u.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  metis_tac[cp_rel_trans]
QED

Theorem call_prefix_contexts:
  cp_rel s t ∧ s.contexts ≠ [] ⇒
  t.contexts ≠ [] ∧ LENGTH t.contexts = LENGTH s.contexts
Proof
  rw[cp_rel_def] >> Cases_on `s.contexts` >> gvs[]
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
  rw[preserves_when_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> drule_all call_prefix_contexts >> strip_tac
  >> first_x_assum drule >> simp[] >> strip_tac
  >> imp_res_tac call_prefix_contexts
  >> gvs[]
  >- (irule cp_rel_trans >> qexists_tac `s` >> simp[])
  >> strip_tac >> gvs[]
QED

Theorem call_prefix_of_cp_keys:
  cp m ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) m ⇒
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) m
Proof
  rw[cp_eq_preserves_when, preserves_when_def] >> metis_tac[]
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
  rw[preserves_when_def, pop_stack_def, memory_expansion_info_def,
     consume_gas_def, assert_not_static_def, expand_memory_def,
     set_return_data_def, get_static_def, get_current_context_def,
     set_current_context_def, bind_def, ignore_bind_def, return_def,
     assert_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

Theorem call_prefix_keys_access_address:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (access_address a)
Proof
  rw[preserves_when_def, access_address_def, domain_check_def,
     set_domain_def, ignore_bind_def, bind_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
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
  rw[preserves_when_def, get_accounts_def, get_gas_left_def,
     get_callee_def, get_num_contexts_def, get_current_context_def,
     bind_def, return_def, fail_def] >> gvs[AllCaseEqs()]
QED

Theorem call_prefix_bind:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) g ∧
  (∀x. preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (f x)) ⇒
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (bind g f)
Proof
  strip_tac >> irule preserves_when_bind >> simp[]
  >> metis_tac[call_prefix_trans, call_prefix_contexts]
QED

Theorem call_prefix_ignore_bind:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) g ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) f ⇒
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (ignore_bind g f)
Proof
  simp[ignore_bind_def] >> strip_tac >> irule call_prefix_bind >> simp[]
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
  rpt conj_tac >> irule call_prefix_of_cp_keys
  >> simp[call_prefix_keys_leaves, call_prefix_keys_access_address,
          call_prefix_keys_getters]
QED

Theorem call_prefix_delegate_selection:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys)
    (case get_delegate acc.code of
       NONE => return (acc.code, 0)
     | SOME d => do
         cost <- access_address d;
         return ((lookup_account d accounts).code, cost)
       od)
Proof
  Cases_on `get_delegate acc.code` >> simp[call_prefix_leaves]
  >> irule call_prefix_bind >> simp[call_prefix_leaves]
QED


Theorem proceed_call_saved_rollback:
  proceed_call op sender address value ao az code gas rd s = (r, s') ∧
  s.contexts ≠ [] ∧ ¬fIN address precompile_addresses ⇒
  SND (HD s'.contexts) = s.rollback ∧
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  strip_tac >> Cases_on `op ≠ CallCode ∧ 0 < value`
  >> gvs[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_current_context_def,
       get_caller_def, get_value_def, get_static_def,
       push_context_def, update_accounts_def, return_def, fail_def,
       AllCaseEqs()]
QED

Theorem proceed_call_nonprecompile_frame:
  proceed_call op sender address value ao az code gas rd s = (r, s') ∧
  s.contexts ≠ [] ∧ ¬fIN address precompile_addresses ⇒
  ∃static t.
    FST (HD s'.contexts) =
      initial_context (if op = CallCode ∨ op = DelegateCall then sender else address)
        code static rd t ∧
    s'.rollback.accounts =
      (if op ≠ CallCode ∧ 0 < value then
         transfer_value sender address value s.rollback.accounts
       else s.rollback.accounts)
Proof
  strip_tac >> Cases_on `op ≠ CallCode ∧ 0 < value`
  >> gvs[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_current_context_def,
       get_caller_def, get_value_def, get_static_def,
       push_context_def, update_accounts_def, return_def, fail_def,
       AllCaseEqs()]
  >> metis_tac[]
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
  cheat
QED

(* The frame a push enters as a new callee: a CALL or STATICCALL running the
 * target's code (or its EIP-7702 delegate's), or a CREATE at an address
 * that is not yet created. *)
Theorem step_push_new_frame:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ∧
  (FST (HD s'.contexts)).msgParams.callee ≠
    (FST (HD s.contexts)).msgParams.callee ⇒
  ∃code static rd t.
    FST (HD s'.contexts) =
      initial_context (FST (HD s'.contexts)).msgParams.callee
        code static rd t ∧
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
  cheat
QED

(* Domain collection mode is never left. *)
Theorem step_preserves_collect:
  (∃d. s.msdomain = Collect d) ∧ step s = (r, s') ⇒
  ∃d. s'.msdomain = Collect d
Proof
  cheat
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
  cheat
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
  cheat
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

Theorem run_call_account_frame:
  wf_state es ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  P (lookup_account a es.rollback.accounts) ∧
  (2 ≤ LENGTH es.contexts ⇒
     P (lookup_account a (SND (HD es.contexts)).accounts)) ∧
  (∀e r e'.
     (FST (HD e.contexts)).msgParams.callee = a ∧
     wf_state e ∧ P (lookup_account a e.rollback.accounts) ∧
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
  cheat
QED

(* -------------------------------------------------------------------------
 * Accounts with no code.
 * ------------------------------------------------------------------------- *)

(* A frame running empty code stops at once; if the callee has no code, a
 * code deposit leaves it so. *)
Theorem run_call_empty_code_frame:
  wf_state e ∧
  (FST (HD e.contexts)).msgParams.code = [] ∧
  (lookup_account (FST (HD e.contexts)).msgParams.callee
     e.rollback.accounts).code = [] ∧
  run_call e = SOME (r, e') ⇒
  e'.rollback.accounts = e.rollback.accounts
Proof
  cheat
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
  cheat
QED

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
  cheat
QED

Theorem step_push_storage_keys:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  (SND (HD s'.contexts)).accesses.storageKeys =
    s.rollback.accesses.storageKeys
Proof
  cheat
QED

(* Every storage key run_call adds for `a` was added by a step executing as
 * `a`, from a reached state. *)
Theorem run_call_storage_key_added:
  wf_state es ∧
  (2 ≤ LENGTH es.contexts ⇒
     toSet (SND (HD es.contexts)).accesses.storageKeys ⊆
     toSet es.rollback.accesses.storageKeys) ∧
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
  cheat
QED
