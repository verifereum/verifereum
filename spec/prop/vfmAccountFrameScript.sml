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
  vfmSameFrame vfmRunWithinFrame vfmRunCall vfmStaticCalls vfmDecreasesGas
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

Theorem cp_preserves_account_prefix[local]:
  cp m ∧ s.contexts ≠ [] ∧
  s.rollback.accounts = A ∧
  EVERY (λ(c,rb). P c.msgParams rb) (TAKE k s.contexts) ∧
  m s = (r,s') ⇒
  s'.rollback.accounts = A ∧
  LENGTH s'.contexts = LENGTH s.contexts ∧
  EVERY (λ(c,rb). P c.msgParams rb) (TAKE k s'.contexts)
Proof
  rw[cp_def]
  >> first_x_assum drule
  >> disch_then drule >> strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `k` >> gvs[]
QED

Theorem account_prefix_bind[local]:
  (∀s. Q s ⇒ Q (SND (g s))) ∧
  (∀x s. Q s ⇒ Q (SND (f x s))) ⇒
  ∀s. Q s ⇒ Q (SND (bind g f s))
Proof
  rpt strip_tac
  >> simp[bind_def]
  >> Cases_on `g s` >> Cases_on `q` >> gvs[]
  >> metis_tac[SND]
QED

Theorem account_prefix_ignore_bind[local]:
  (∀s. Q s ⇒ Q (SND (g s))) ∧
  (∀s. Q s ⇒ Q (SND (f s))) ⇒
  ∀s. Q s ⇒ Q (SND (ignore_bind g f s))
Proof
  strip_tac >> rewrite_tac[ignore_bind_def]
  >> ho_match_mp_tac account_prefix_bind >> simp[]
QED

Theorem account_prefix_static_guard[local]:
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (ignore_bind assert_not_static f s))
Proof
  rpt strip_tac
  >> `s.contexts ≠ [] ∧ (FST (HD s.contexts)).msgParams.static`
    by metis_tac[]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> drule_all assert_not_static_static
  >> simp[ignore_bind_def, bind_def]
QED

Theorem account_prefix_conditional_guard[local]:
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ∧
  (¬b ⇒ ∀s. Q s ⇒ Q (SND (f s))) ⇒
  ∀s. Q s ⇒
    Q (SND (ignore_bind (if b then assert_not_static else return ()) f s))
Proof
  Cases_on `b`
  >- (simp[] >> MATCH_ACCEPT_TAC account_prefix_static_guard)
  >> simp[ignore_bind_def, bind_def, return_def]
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
  rw[cp_def]
  >> `s.contexts ≠ []` by (strip_tac >> gvs[])
  >> Cases_on `m s` >> gvs[]
  >> first_x_assum drule >> disch_then drule >> strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `LENGTH t + 2 - n` >> gvs[]
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
  strip_tac >> gen_tac >> disch_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> `LENGTH t + 2 - n = SUC (LENGTH t + 1 - n)` by decide_tac
  >> gvs[]
  >> simp[proceed_call_def, bind_def, ignore_bind_def, return_def,
          get_rollback_def, read_memory_def,
          get_caller_def, get_value_def, get_static_def,
          get_current_context_def, push_context_def,
          initial_context_def, initial_msg_params_def]
  >> qmatch_goalsub_abbrev_tac `SND (f pushed)`
  >> `cp f` by simp[Abbr `f`]
  >> `pushed.contexts ≠ []` by simp[Abbr `pushed`]
  >> Cases_on `f pushed` >> gvs[]
  >> qpat_x_assum `cp f` mp_tac >> rewrite_tac[cp_def]
  >> disch_then drule >> disch_then drule >> strip_tac
  >> gvs[Abbr `pushed`]
  >> qpat_x_assum `EVERY _ _` mp_tac
  >> `SUC (SUC (LENGTH t)) - (n + 1) = SUC (LENGTH t) - n` by decide_tac
  >> pop_assum SUBST1_TAC >> simp[]
QED

Theorem account_prefix_cp[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ []) ∧ cp m ⇒
  ∀s. Q s ⇒ Q (SND (m s))
Proof
  rw[cp_def]
  >> `s.contexts ≠ []` by metis_tac[]
  >> Cases_on `m s` >> gvs[]
  >> first_x_assum drule >> simp[] >> strip_tac
  >> first_x_assum irule
  >> qexists_tac `s` >> simp[cp_rel_def]
QED

Theorem account_prefix_bind_cp[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ []) ∧ cp g ∧
  (∀x s. Q s ⇒ Q (SND (f x s))) ⇒
  ∀s. Q s ⇒ Q (SND (bind g f s))
Proof
  strip_tac >> ho_match_mp_tac account_prefix_bind
  >> simp[] >> ho_match_mp_tac account_prefix_cp
  >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem account_prefix_ignore_bind_cp[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ []) ∧ cp g ∧
  (∀s. Q s ⇒ Q (SND (f s))) ⇒
  ∀s. Q s ⇒ Q (SND (ignore_bind g f s))
Proof
  strip_tac >> ho_match_mp_tac account_prefix_ignore_bind
  >> simp[] >> ho_match_mp_tac account_prefix_cp
  >> simp[] >> first_assum ACCEPT_TAC
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
  strip_tac >> simp[step_call_def, LET_THM]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac >> pairarg_tac >> simp[]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac >> PairCases_on `x` >> simp[]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac >> pairarg_tac >> simp[]
  >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_conditional_guard
  >> conj_tac >- (first_assum ACCEPT_TAC)
  >> strip_tac
  >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> IF_CASES_TAC
  >- (ho_match_mp_tac account_prefix_cp >> simp[SF ETA_ss] >> first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> IF_CASES_TAC
  >- (ho_match_mp_tac account_prefix_cp >> simp[SF ETA_ss] >> first_assum ACCEPT_TAC)
  >> first_x_assum ho_match_mp_tac
  >> Cases_on `op` >> gvs[call_has_value_def]
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
  rw[cp_rel_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `LENGTH t + 2 - n` >> gvs[]
QED

Theorem static_prefix_head[local]:
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ⇒
  s.contexts ≠ [] ∧ (FST (HD s.contexts)).msgParams.static
Proof
  Cases_on `s.contexts` >- (strip_tac >> gvs[])
  >> PairCases_on `h` >> simp[] >> strip_tac
  >> `LENGTH t + 2 - n = SUC (LENGTH t + 1 - n)` by decide_tac
  >> gvs[]
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
  match_mp_tac (BETA_RULE (Q.INST [`Q` |->
    `λs. 0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
      EVERY (λ(c,rb). c.msgParams.static ∧
        (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
        (TAKE (LENGTH s.contexts - n + 1) s.contexts)`]
    account_prefix_step_call))
  >> rpt conj_tac
  >- (rpt strip_tac >> drule_all static_prefix_cp_rel >> simp[])
  >- (rpt strip_tac >> drule_all static_prefix_head >> simp[])
  >> rpt gen_tac >> disch_tac
  >> match_mp_tac proceed_call_preserves_static_prefix >> simp[]
QED

Theorem account_prefix_sstore[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_sstore transient s))
Proof
  strip_tac >> simp[step_sstore_def, LET_THM]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_static_guard
  >> first_assum ACCEPT_TAC
QED

Theorem account_prefix_log[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_log num s))
Proof
  strip_tac >> simp[step_log_def, LET_THM]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_static_guard
  >> first_assum ACCEPT_TAC
QED

Theorem account_prefix_self_destruct[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_self_destruct s))
Proof
  strip_tac >> simp[step_self_destruct_def, LET_THM]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_static_guard
  >> first_assum ACCEPT_TAC
QED

Theorem account_prefix_create[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_create two s))
Proof
  strip_tac >> simp[step_create_def, LET_THM]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_static_guard
  >> first_assum ACCEPT_TAC
QED

Theorem account_prefix_step_inst[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ∧
  (∀op s. Q s ⇒ Q (SND (step_call op s))) ⇒
  ∀s. Q s ⇒ Q (SND (step_inst op s))
Proof
  strip_tac >> Cases_on `op`
  >~ [`step_inst SStore`] >- (
    rewrite_tac[step_inst_def]
    >> ho_match_mp_tac account_prefix_sstore >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst TStore`] >- (
    rewrite_tac[step_inst_def]
    >> ho_match_mp_tac account_prefix_sstore >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst (Log _)`] >- (
    rewrite_tac[step_inst_def]
    >> ho_match_mp_tac account_prefix_log >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst SelfDestruct`] >- (
    rewrite_tac[step_inst_def]
    >> match_mp_tac account_prefix_self_destruct >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst Create`] >- (
    rewrite_tac[step_inst_def]
    >> ho_match_mp_tac account_prefix_create >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst Create2`] >- (
    rewrite_tac[step_inst_def]
    >> ho_match_mp_tac account_prefix_create >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst Call`] >- simp[step_inst_def]
  >~ [`step_inst CallCode`] >- simp[step_inst_def]
  >~ [`step_inst DelegateCall`] >- simp[step_inst_def]
  >~ [`step_inst StaticCall`] >- simp[step_inst_def]
  >> ho_match_mp_tac account_prefix_cp
  >> simp[SF ETA_ss] >> first_assum ACCEPT_TAC
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
  match_mp_tac (BETA_RULE (Q.INST [`Q` |->
    `λs. 0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
      EVERY (λ(c,rb). c.msgParams.static ∧
        (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
        (TAKE (LENGTH s.contexts - n + 1) s.contexts)`]
    account_prefix_step_inst))
  >> rpt conj_tac
  >- (rpt strip_tac >> drule_all static_prefix_cp_rel >> simp[])
  >- (rpt strip_tac >> drule_all static_prefix_head >> simp[])
  >> gen_tac >> MATCH_ACCEPT_TAC step_call_preserves_static_prefix
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
  strip_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> qx_gen_tac `ctxt` >> Cases_on `FLOOKUP ctxt.msgParams.parsed ctxt.pc`
  >- (simp[] >> IF_CASES_TAC >> first_assum MATCH_ACCEPT_TAC)
  >> simp[] >> ho_match_mp_tac account_prefix_ignore_bind
  >> conj_tac >- (first_assum MATCH_ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_cp
  >> simp[SF ETA_ss] >> first_assum ACCEPT_TAC
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
  strip_tac
  >> mp_tac (BETA_RULE (Q.INST [`Q` |->
    `λs. 0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
      EVERY (λ(c,rb). c.msgParams.static ∧
        (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
        (TAKE (LENGTH s.contexts - n + 1) s.contexts)`]
    account_prefix_inner))
  >> impl_tac
  >- (rpt conj_tac
      >- (rpt strip_tac >> drule_all static_prefix_cp_rel >> simp[])
      >- (rpt strip_tac >> drule_all static_prefix_head >> simp[])
      >> gen_tac >> MATCH_ACCEPT_TAC step_inst_preserves_static_prefix)
  >> disch_then (qspec_then `s` mp_tac) >> simp[]
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
  strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `t` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> `LENGTH t' + 3 - n = SUC (LENGTH t' + 2 - n)` by decide_tac
  >> gvs[]
  >> simp[pop_and_incorporate_context_def, bind_def,
    get_gas_left_def, get_current_context_def, return_def,
    pop_context_def, unuse_gas_def, LET_THM,
    set_current_context_def, fail_def, assert_def, ignore_bind_def]
  >> Cases_on `success`
  >> simp[push_logs_def, bind_def, get_current_context_def,
    set_current_context_def, return_def, update_gas_refund_def, set_rollback_def]
  >> IF_CASES_TAC >> gvs[]
  >> strip_tac
  >> `LENGTH t' + 2 - n = SUC (LENGTH t' + 1 - n)` by decide_tac
  >> gvs[]
  >> `SUC (SUC (LENGTH t')) - (n + 1) = SUC (LENGTH t') - n` by decide_tac
  >> pop_assum SUBST_ALL_TAC >> simp[]
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
  rw[cp_def]
  >> first_x_assum drule >> disch_then drule >> strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `LENGTH t + 2 - n` >> gvs[]
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
  strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> simp[handle_ex_helper_def, bind_def, get_num_contexts_def,
    get_current_context_def, return_def, fail_def]
  >> Cases_on `t`
  >- simp[reraise_def]
  >> simp[bind_def, get_return_data_def, get_output_to_def,
    get_current_context_def, return_def, ignore_bind_def]
  >> `1 < LENGTH s.contexts` by simp[]
  >> mp_tac (Q.INST [`A` |-> `s.rollback.accounts`,
      `success` |-> `(e : exception option) = NONE`] pop_incorporate_account_prefix)
  >> impl_tac >- gvs[]
  >> strip_tac
  >> Cases_on `pop_and_incorporate_context (e = NONE) s`
  >> Cases_on `q` >> gvs[]
  >> `r.contexts ≠ []`
    by (irule pop_incorporate_contexts_ne
        >> goal_assum (drule_at Any) >> simp[])
  >> Cases_on `after_pop h0.returnData h0.msgParams.outputTo (e = NONE) r`
  >> gvs[]
  >> drule_at (Pos (el 5)) cp_preserves_account_prefix_exit
  >> disch_then (qspecl_then [`n`, `s.rollback.accounts`] mp_tac)
  >> simp[]
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
  strip_tac >> simp[handle_exception_decomp, LET_THM]
  >> qmatch_goalsub_abbrev_tac `bind prefix _ s`
  >> `cp prefix` by simp[Abbr `prefix`]
  >> drule cp_preserves_static_prefix
  >> disch_then (qspecl_then [`n`, `A`, `s`] mp_tac)
  >> simp[] >> strip_tac
  >> simp[bind_def]
  >> Cases_on `prefix s` >> Cases_on `q` >> gvs[]
  >> mp_tac (Q.INST [`s` |-> `r`, `A` |-> `s.rollback.accounts`]
      handle_ex_helper_account_prefix)
  >> simp[]
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
  strip_tac
  >> `s.contexts ≠ []` by (strip_tac >> gvs[])
  >> `(∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a)` by
    (Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> gvs[]
     >> `LENGTH t + 2 - n = SUC (LENGTH t + 1 - n)` by decide_tac
     >> gvs[])
  >> simp[handle_step_def]
  >> IF_CASES_TAC >- gvs[reraise_def]
  >> drule_all (INST_TYPE [alpha |-> ``:unit``] handle_create_reraises)
  >> simp[handle_def, reraise_def]
  >> strip_tac >> mp_tac handle_exception_account_prefix >> gvs[]
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
  strip_tac
  >> `wf_state s'` by (drule step_preserves_wf_state >> simp[])
  >> simp[]
  >> qpat_x_assum `step s = _` mp_tac
  >> simp[step_def, LET_THM]
  >> qmatch_goalsub_abbrev_tac `handle inner handle_step s`
  >> `∀r s'. inner s = (r,s') ⇒
       0 < n ∧ n ≤ LENGTH s'.contexts ∧ s'.rollback.accounts = A ∧
       EVERY (λ(c,rb). c.msgParams.static ∧
         (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
         (TAKE (LENGTH s'.contexts - n + 1) s'.contexts)` by
    (map_every qx_gen_tac [`res`, `st`] >> disch_tac
     >> irule inner_preserves_static_prefix >> conj_tac >- simp[]
     >> map_every qexists_tac [`res`, `s`] >> gvs[Abbr `inner`])
  >> simp[handle_def]
  >> Cases_on `inner s` >> Cases_on `q` >> gvs[]
  >- (strip_tac >> gvs[])
  >> rename1 `inner s = (INR ex, mid)`
  >> mp_tac (Q.INST [`s` |-> `mid`, `e` |-> `ex`,
       `A` |-> `s.rollback.accounts`] handle_step_account_prefix)
  >> simp[] >> strip_tac >> Cases_on `handle_step ex mid` >> gvs[]
  >> strip_tac >> gvs[]
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
  strip_tac
  >> `0 < LENGTH e.contexts` by (gvs[wf_state_def] >> Cases_on `e.contexts` >> gvs[])
  >> gvs[run_call_def]
  >> `(λp. wf_state (SND p) ∧
       (SND p).rollback.accounts = e.rollback.accounts ∧
       (LENGTH e.contexts ≤ LENGTH (SND p).contexts ⇒
        EVERY (λ(c,rb). c.msgParams.static ∧
          (∀a. c.msgParams.outputTo ≠ Code a) ∧
          rb.accounts = e.rollback.accounts)
          (TAKE (LENGTH (SND p).contexts - LENGTH e.contexts + 1)
                (SND p).contexts))) (r,e')` suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum $ drule_at Any
  >> simp[]
  >> conj_tac
  >- (Cases_on `e.contexts` >> gvs[] >> PairCases_on `h` >> gvs[])
  >> qx_gen_tac `p` >> PairCases_on `p` >> simp[]
  >> strip_tac >> Cases_on `step p1` >> simp[]
  >> mp_tac (Q.INST [`s` |-> `p1`, `s'` |-> `r'`, `r` |-> `q`,
       `n` |-> `LENGTH e.contexts`, `A` |-> `e.rollback.accounts`]
       step_preserves_static_account_prefix)
  >> simp[]
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
  cheat
QED

(* -------------------------------------------------------------------------
 * Accounts with no code.
 * ------------------------------------------------------------------------- *)

Theorem step_empty_code[local]:
  wf_state e ∧ (FST (HD e.contexts)).msgParams.code = [] ⇒
  step e = handle (step_inst Stop) handle_step e
Proof
  strip_tac
  >> `e.contexts ≠ [] ∧ EVERY (wf_context o FST) e.contexts` by
       gvs[wf_state_def]
  >> Cases_on `e.contexts` >> gvs[] >> PairCases_on `h` >> gvs[]
  >> `h0.msgParams.parsed = FEMPTY` by
       (qpat_x_assum `wf_context h0` mp_tac
        >> simp[wf_context_def, Once parse_code_def])
  >> simp[step_def, get_current_context_def, bind_def, return_def,
          LET_THM, handle_def]
QED

Theorem handle_exception_success_accounts[local]:
  handle_exception NONE s = (r,s') ⇒
  s'.rollback.accounts = s.rollback.accounts
Proof
  Cases_on `s.contexts` >- simp[handle_exception_def, get_num_contexts_def,
    bind_def, ignore_bind_def, return_def, reraise_def]
  >> Cases_on `t`
  >- simp[handle_exception_def, get_num_contexts_def,
    bind_def, ignore_bind_def, return_def, reraise_def]
  >> PairCases_on `h` >> PairCases_on `h'`
  >> Cases_on `h0.msgParams.outputTo`
  >> simp[handle_exception_def, bind_def, ignore_bind_def,
     get_num_contexts_def, get_current_context_def, return_def,
     get_return_data_def, get_output_to_def, reraise_def,
     pop_and_incorporate_context_def, get_gas_left_def, pop_context_def,
     unuse_gas_def, assert_def, fail_def, set_current_context_def,
     push_logs_def, update_gas_refund_def, inc_pc_def,
     set_return_data_def, push_stack_def, write_memory_def,
     AllCaseEqs()]
  >> rpt strip_tac >> gvs[]
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
  Cases_on `s.contexts` >> simp[] >> PairCases_on `h`
  >> simp[wf_context_def, outputTo_consistent_ctx_def]
  >> strip_tac
  >> Cases_on `h0.msgParams.outputTo`
  >> simp[handle_create_def, get_return_data_def, get_output_to_def,
      get_current_context_def, bind_def, ignore_bind_def, return_def,
      reraise_def, assert_def, consume_gas_def, set_current_context_def,
      update_accounts_def, LET_THM]
  >> `h0.msgParams.callee = c` by metis_tac[]
  >> `update_account c (lookup_account c s.rollback.accounts with code := [])
         s.rollback.accounts = s.rollback.accounts` by
       (gvs[lookup_account_def, update_account_def, FUN_EQ_THM,
            combinTheory.APPLY_UPDATE_THM]
        >> gen_tac >> IF_CASES_TAC >> gvs[]
        >> simp[account_state_component_equality])
  >> simp[execution_state_component_equality, rollback_state_component_equality]
QED

Theorem step_empty_code_exit[local]:
  wf_state e ∧ (FST (HD e.contexts)).msgParams.code = [] ∧
  (lookup_account (FST (HD e.contexts)).msgParams.callee
    e.rollback.accounts).code = [] ∧ step e = (r,s) ⇒
  s.rollback.accounts = e.rollback.accounts ∧
  (¬ISL r ∨ LENGTH s.contexts < LENGTH e.contexts)
Proof
  strip_tac
  >> `step e = handle (step_inst Stop) handle_step e` by
       (irule step_empty_code >> simp[])
  >> `e.contexts ≠ [] ∧ EVERY (wf_context o FST) e.contexts ∧
       outputTo_consistent_stack e` by gvs[wf_state_def]
  >> Cases_on `e.contexts` >> gvs[] >> PairCases_on `h` >> gvs[]
  >> qpat_x_assum `handle _ _ _ = _` mp_tac
  >> simp[step_inst_def, set_return_data_def, finish_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `handle_step NONE mid`
  >> `(handle_create NONE mid : (unit + exception option) # execution_state) = (INR NONE,mid)` by
       (irule handle_create_empty_identity
        >> gvs[Abbr `mid`, outputTo_consistent_stack_def,
               outputTo_consistent_ctx_def, wf_context_def])
  >> simp[handle_step_def, vfm_abort_def, handle_def]
  >> strip_tac >> gvs[]
  >> conj_tac
  >- (drule handle_exception_success_accounts >> simp[Abbr `mid`])
  >> Cases_on `t`
  >- (qpat_x_assum `handle_exception _ _ = _` mp_tac
      >> simp[Abbr `mid`, handle_exception_def, get_num_contexts_def,
              bind_def, ignore_bind_def, return_def, reraise_def]
      >> strip_tac >> gvs[])
  >> disj2_tac
  >> `EVERY (wf_context o FST) mid.contexts ∧ LENGTH mid.contexts ≥ 2` by
       gvs[Abbr `mid`, wf_context_def]
  >> drule_all vfmHandleStepTheory.handle_exception_ge_2_pops
  >> simp[Abbr `mid`]
QED

Theorem run_call_empty_code_frame:
  wf_state e ∧
  (FST (HD e.contexts)).msgParams.code = [] ∧
  (lookup_account (FST (HD e.contexts)).msgParams.callee
     e.rollback.accounts).code = [] ∧
  run_call e = SOME (r, e') ⇒
  e'.rollback.accounts = e.rollback.accounts
Proof
  strip_tac
  >> Cases_on `step e`
  >> drule_all step_empty_code_exit >> strip_tac
  >> qpat_x_assum `run_call _ = _` mp_tac
  >> simp[run_call_def, Once OWHILE_THM]
  >> simp[Once OWHILE_THM]
  >> strip_tac >> gvs[]
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

(* -------------------------------------------------------------------------
 * Deletions.  SELFDESTRUCT schedules its callee for deletion only if the
 * callee is empty in the original accounts (the LAST saved rollback),
 * which only a CREATE at that address changes.  A CREATE needs the address
 * not yet created, which an account with a nonce or code never becomes
 * again within run_call.
 * ------------------------------------------------------------------------- *)

Theorem run_call_to_delete:
  wf_state es ∧
  run_call es = SOME (r, es') ∧
  MEM a es'.rollback.toDelete ⇒
  MEM a es.rollback.toDelete ∨
  (2 ≤ LENGTH es.contexts ∧ MEM a (SND (HD es.contexts)).toDelete) ∨
  account_empty (lookup_account a (SND (LAST es.contexts)).accounts) ∨
  (lookup_account a es.rollback.accounts).nonce = 0 ∧
  NULL (lookup_account a es.rollback.accounts).code
Proof
  cheat
QED
