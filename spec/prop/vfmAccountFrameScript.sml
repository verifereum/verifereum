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
  vfmSameFrame vfmRunWithinFrame vfmRunCall
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

Theorem OWHILE_finite_trace:
  OWHILE G f x = SOME y ⇒
  ∃n. FUNPOW f n x = y ∧ ¬G y ∧
      ∀k. k < n ⇒ G (FUNPOW f k x)
Proof
  rw[OWHILE_def]
  >> qexists_tac `LEAST n. ¬G (FUNPOW f n x)`
  >> numLib.LEAST_ELIM_TAC >> metis_tac[]
QED

Theorem OWHILE_from_finite_trace:
  ∀n x. ¬G (FUNPOW f n x) ∧
    (∀k. k < n ⇒ G (FUNPOW f k x)) ⇒
    OWHILE G f x = SOME (FUNPOW f n x)
Proof
  Induct >> rw[]
  >- simp[Once OWHILE_THM]
  >> `G x` by (first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >> simp[Once OWHILE_THM]
  >> fs[FUNPOW]
  >> first_x_assum irule >> simp[]
  >> rpt strip_tac
  >> first_x_assum (qspec_then `SUC k` mp_tac)
  >> simp[FUNPOW]
QED

Theorem OWHILE_nested_trace:
  (∀z. H z ⇒ G z) ∧ ¬G (FUNPOW f n x) ⇒
  ∃m. m ≤ n ∧
      OWHILE H f x = SOME (FUNPOW f m x) ∧
      ¬H (FUNPOW f m x) ∧
      (∀k. k < m ⇒ H (FUNPOW f k x))
Proof
  strip_tac
  >> qexists_tac `LEAST m. ¬H (FUNPOW f m x)`
  >> numLib.LEAST_ELIM_TAC
  >> conj_tac >- metis_tac[]
  >> rpt strip_tac
  >- (spose_not_then assume_tac >>
      rename1 `¬(j ≤ n)` >>
      `n < j` by decide_tac >> metis_tac[])
  >- (irule OWHILE_from_finite_trace >> metis_tac[])
  >> metis_tac[]
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
  rw[run_call_def]
  >> drule OWHILE_finite_trace
  >> strip_tac >> qexists_tac `n` >> gvs[GREATER_EQ]
  >> rpt strip_tac
  >> first_x_assum drule
  >> pairarg_tac >> simp[GREATER_EQ]
QED

Theorem run_call_trace_reaches:
  ∀n. (∀k. k < n ⇒
          ISL (FST (FUNPOW (step o SND) k (INL (), es))) ∧
          LENGTH es.contexts ≤
            LENGTH (SND (FUNPOW (step o SND) k (INL (), es))).contexts) ∧
      ISL (FST (FUNPOW (step o SND) n (INL (), es))) ⇒
      run_call_reaches es (SND (FUNPOW (step o SND) n (INL (), es)))
Proof
  Induct >- simp[]
  >> strip_tac
  >> `ISL (FST (FUNPOW (step o SND) n (INL (), es))) ∧
      LENGTH es.contexts ≤
        LENGTH (SND (FUNPOW (step o SND) n (INL (), es))).contexts`
       by (first_x_assum (qspec_then `n` mp_tac) >> simp[])
  >> `run_call_reaches es (SND (FUNPOW (step o SND) n (INL (), es)))`
       by (first_x_assum irule >> simp[] >> rpt strip_tac >>
           first_x_assum irule >> decide_tac)
  >> gvs[FUNPOW_SUC]
  >> qmatch_goalsub_abbrev_tac `step s`
  >> `LENGTH es.contexts ≤ LENGTH s.contexts`
       by (first_x_assum (qspec_then `n` mp_tac) >> simp[Abbr`s`])
  >> Cases_on `step s` >> gvs[]
  >> Cases_on `q` >> gvs[]
  >> irule run_call_reaches_step >> metis_tac[]
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
  strip_tac >> simp[run_call_def, GREATER_EQ]
  >> irule OWHILE_nested_trace
  >> qexists_tac `λ(r,s). ISL r ∧ d ≤ LENGTH s.contexts`
  >> simp[FORALL_PROD] >> rpt strip_tac >> decide_tac
QED

Theorem OWHILE_trace_continuation:
  (∀k. k < n ⇒ G (FUNPOW f k x)) ∧ m ≤ n ⇒
  OWHILE G f x = OWHILE G f (FUNPOW f m x)
Proof
  strip_tac >> irule OWHILE_RTC
  >> `∀j. j ≤ n ⇒ RTC (λx y. G x ∧ f x = y) x (FUNPOW f j x)`
       suffices_by metis_tac[]
  >> Induct >- simp[]
  >> strip_tac >> simp[FUNPOW_SUC]
  >> irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1))
  >> qexists_tac `FUNPOW f j x`
  >> simp[]
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

Theorem active_rollbacks_initial:
  Q es.rollback ∧
  (2 ≤ LENGTH es.contexts ⇒ Q (SND (HD es.contexts))) ⇒
  EVERY Q (active_rollbacks (LENGTH es.contexts) es)
Proof
  rw[active_rollbacks_def]
  >> Cases_on `es.contexts` >> gvs[]
  >> Cases_on `t` >> gvs[MIN_DEF]
  >> rw[] >> gvs[]
  >> `LENGTH t' = 0` by decide_tac >> gvs[]
QED

Theorem active_rollbacks_same_stack:
  LENGTH t.contexts = LENGTH s.contexts ∧
  TL t.contexts = TL s.contexts ∧
  SND (HD t.contexts) = SND (HD s.contexts) ⇒
  TL (active_rollbacks d t) = TL (active_rollbacks d s)
Proof
  strip_tac >> simp[active_rollbacks_def]
  >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[]
  >> qmatch_goalsub_abbrev_tac `TAKE k (h::t')`
  >> Cases_on `k` >> simp[]
QED

Theorem step_same_frame_account_invariant:
  wf_state s ∧ step s = (r,t) ∧
  LENGTH t.contexts = LENGTH s.contexts ∧
  (FST (HD s.contexts)).msgParams.callee ≠ a ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d s) ⇒
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d t)
Proof
  strip_tac
  >> drule_all step_same_frame_foreign >> strip_tac
  >> `TL (active_rollbacks d t) = TL (active_rollbacks d s)`
       by (irule active_rollbacks_same_stack >> simp[])
  >> `P (lookup_account a s.rollback.accounts)`
       by gvs[active_rollbacks_def]
  >> `P (lookup_account a t.rollback.accounts)` by metis_tac[]
  >> `EVERY (λrb. P (lookup_account a rb.accounts))
            (TL (active_rollbacks d s))` by gvs[active_rollbacks_def]
  >> `EVERY (λrb. P (lookup_account a rb.accounts))
            (TL (active_rollbacks d t))` by metis_tac[]
  >> gvs[active_rollbacks_def]
QED

Theorem active_rollbacks_push_tail:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  FRONT (TL (TL t.contexts)) = FRONT (TL s.contexts) ∧
  (2 ≤ LENGTH s.contexts ⇒ SND (EL 1 t.contexts) = SND (HD s.contexts)) ⇒
  TL (active_rollbacks d t) =
    SND (HD t.contexts) :: TL (active_rollbacks d s)
Proof
  strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `t.contexts` >> gvs[]
  >> Cases_on `t'` >> gvs[]
  >> Cases_on `t` >> gvs[active_rollbacks_def, MIN_DEF]
  >> rw[] >> gvs[]
  >> rename1 `FRONT (TL ys) = FRONT (z::zs)`
  >> Cases_on `ys` >> gvs[]
  >> simp[ADD1]
  >> AP_TERM_TAC
  >> qmatch_goalsub_abbrev_tac `TAKE k _`
  >> `k < LENGTH t ∧ k < LENGTH (z::zs)` by (simp[Abbr `k`] >> decide_tac)
  >> metis_tac[TAKE_FRONT, NOT_CONS_NIL, LENGTH_NIL, prim_recTheory.NOT_LESS_0]
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
  strip_tac >> drule_all step_push_foreign >> strip_tac
  >> `TL (active_rollbacks d t) =
       SND (HD t.contexts) :: TL (active_rollbacks d s)`
       by (irule active_rollbacks_push_tail >> simp[])
  >> `P (lookup_account a s.rollback.accounts) ∧
      EVERY (λrb. P (lookup_account a rb.accounts))
        (TL (active_rollbacks d s))` by gvs[active_rollbacks_def]
  >> `P (lookup_account a t.rollback.accounts) ∧
      P (lookup_account a (SND (HD t.contexts)).accounts)` by metis_tac[]
  >> Cases_on `active_rollbacks d t` >> gvs[active_rollbacks_def]
QED

Theorem active_rollbacks_pop:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  s.contexts = h::parent::rest ∧
  t.contexts = (new_head,SND parent)::rest ∧
  EVERY Q (active_rollbacks d s) ⇒
  Q s.rollback ∧ Q (SND h) ∧ EVERY Q (TL (active_rollbacks d t))
Proof
  simp[active_rollbacks_def] >> strip_tac
  >> gvs[MIN_DEF] >> rw[] >> gvs[]
  >> gvs[ADD1]
  >> Cases_on `rest` >> gvs[]
QED

Theorem active_rollbacks_pop_tail:
  0 < d ∧ d ≤ LENGTH t.contexts ∧
  s.contexts = h::parent::rest ∧
  t.contexts = (new_head,SND parent)::rest ⇒
  TL (active_rollbacks d t) = TL (TL (active_rollbacks d s))
Proof
  strip_tac >> simp[active_rollbacks_def]
  >> gvs[MIN_DEF] >> rw[] >> gvs[ADD1]
  >> Cases_on `rest` >> gvs[]
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
  strip_tac >> drule_all step_pop_foreign >> strip_tac
  >> drule_all active_rollbacks_pop >> strip_tac
  >> `P (lookup_account a t.rollback.accounts)` by metis_tac[]
  >> gvs[active_rollbacks_def]
QED

Theorem step_foreign_account_invariant:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  wf_state s ∧ step s = (r,t) ∧
  (FST (HD s.contexts)).msgParams.callee ≠ a ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d s) ⇒
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d t)
Proof
  strip_tac
  >> Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (irule step_same_frame_account_invariant >> metis_tac[])
  >> Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (irule step_push_account_invariant >> metis_tac[])
  >> `LENGTH t.contexts < LENGTH s.contexts` by decide_tac
  >> irule step_pop_account_invariant >> metis_tac[]
QED

Theorem step_outer_saved_rollbacks:
  0 < d ∧ d ≤ k ∧ k < LENGTH s.contexts ∧
  wf_state s ∧ step s = (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (TL (active_rollbacks d t)) =
  DROP (LENGTH s.contexts - k) (TL (active_rollbacks d s))
Proof
  strip_tac
  >> Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`outputTo_consistent s`
        by metis_tac[outputTo_consistent_stack_imp_consistent, wf_state_def]
      >> drule_all step_same_frame >> strip_tac
      >> `TL (active_rollbacks d t) = TL (active_rollbacks d s)`
          by (irule active_rollbacks_same_stack >> gvs[same_frame_rel_def])
      >> simp[])
  >> Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (drule_all step_push_foreign >> strip_tac
      >> `TL (active_rollbacks d t) =
           SND (HD t.contexts) :: TL (active_rollbacks d s)`
           by (irule active_rollbacks_push_tail >> simp[])
      >> `LENGTH t.contexts - k = SUC (LENGTH s.contexts - k)` by decide_tac
      >> simp[])
  >> `LENGTH t.contexts < LENGTH s.contexts` by decide_tac
  >> drule_all step_pop_foreign >> strip_tac
  >> `LENGTH s.contexts = SUC (SUC (LENGTH rest))`
       by (qpat_assum `s.contexts = _` (once_rewrite_tac o single) >> simp[])
  >> `k ≤ LENGTH t.contexts` by (gvs[] >> decide_tac)
  >> `TL (active_rollbacks d t) = TL (TL (active_rollbacks d s))`
       by (irule active_rollbacks_pop_tail >> metis_tac[LESS_EQ_TRANS])
  >> `LENGTH s.contexts - k = SUC (LENGTH t.contexts - k)`
       by (gvs[] >> decide_tac)
  >> simp[DROP_SUC]
  >> once_rewrite_tac[GSYM DROP_SUC]
  >> Cases_on `TL (active_rollbacks d s)` >> simp[]
QED

Theorem run_call_outer_saved_rollbacks:
  0 < d ∧ d ≤ k ∧ k < LENGTH e.contexts ∧
  wf_state e ∧ run_call e = SOME (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (TL (active_rollbacks d t)) =
  DROP (LENGTH e.contexts - k) (TL (active_rollbacks d e))
Proof
  strip_tac >> gvs[run_call_def]
  >> `(λp. wf_state (SND p) ∧ k ≤ LENGTH (SND p).contexts ∧
       DROP (LENGTH (SND p).contexts - k) (TL (active_rollbacks d (SND p))) =
       DROP (LENGTH e.contexts - k) (TL (active_rollbacks d e))) (r,t)`
       suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[] >> rpt gen_tac >> strip_tac
  >> pairarg_tac >> gvs[]
  >> rename1 `LENGTH s.contexts ≥ LENGTH e.contexts`
  >> Cases_on `step s` >> gvs[]
  >> `k < LENGTH s.contexts` by decide_tac
  >> drule_all step_outer_saved_rollbacks >> strip_tac
  >> metis_tac[step_preserves_wf_state, SND]
QED

Theorem run_call_popped_saved_rollbacks:
  0 < d ∧ d < LENGTH e.contexts ∧
  wf_state e ∧ run_call e = SOME (INL (),t) ⇒
  TL (active_rollbacks d t) = TL (TL (active_rollbacks d e))
Proof
  strip_tac
  >> `d ≤ LENGTH e.contexts - 1 ∧ LENGTH e.contexts - 1 < LENGTH e.contexts`
       by decide_tac
  >> `LENGTH e.contexts - 1 ≤ LENGTH t.contexts ∧
       DROP (LENGTH t.contexts - (LENGTH e.contexts - 1)) (TL (active_rollbacks d t)) =
       DROP (LENGTH e.contexts - (LENGTH e.contexts - 1)) (TL (active_rollbacks d e))`
       by (irule run_call_outer_saved_rollbacks >> metis_tac[])
  >> `LENGTH t.contexts < LENGTH e.contexts`
       by (drule run_call_finite_trace >> simp[] >> strip_tac >> decide_tac)
  >> `LENGTH t.contexts = LENGTH e.contexts - 1 ∧
      LENGTH e.contexts - (LENGTH e.contexts - 1) = 1` by decide_tac
  >> gvs[]
  >> Cases_on `TL (active_rollbacks d e)` >> gvs[]
QED

Theorem run_call_saved_account_invariant:
  0 < d ∧ d < LENGTH e.contexts ∧ wf_state e ∧
  EVERY Q (TL (active_rollbacks d e)) ∧
  Q t.rollback ∧ run_call e = SOME (INL (),t) ⇒
  EVERY Q (active_rollbacks d t)
Proof
  strip_tac >> drule_all run_call_popped_saved_rollbacks >> strip_tac
  >> `EVERY Q (TL (TL (active_rollbacks d e)))`
       by (Cases_on `TL (active_rollbacks d e)` >> gvs[])
  >> Cases_on `active_rollbacks d t` >> gvs[active_rollbacks_def]
QED

Theorem step_outer_msgParams:
  0 < k ∧ k < LENGTH s.contexts ∧ wf_state s ∧ step s = (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (MAP (λp. (FST p).msgParams) t.contexts) =
  DROP (LENGTH s.contexts - k) (MAP (λp. (FST p).msgParams) s.contexts)
Proof
  strip_tac
  >> Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`outputTo_consistent s`
        by metis_tac[outputTo_consistent_stack_imp_consistent, wf_state_def]
      >> drule_all step_same_frame >> simp[same_frame_rel_def]
      >> strip_tac
      >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[])
  >> Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (drule_all step_push_foreign >> strip_tac
      >> `MAP (λp. (FST p).msgParams) (TL (TL t.contexts)) =
          MAP (λp. (FST p).msgParams) (TL s.contexts)`
          by metis_tac[MAP_MAP_o, combinTheory.o_DEF]
      >> `LENGTH t.contexts - k = SUC (LENGTH s.contexts - k)` by decide_tac
      >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[]
      >> rename1 `MAP FST (TL cs) = _`
      >> Cases_on `cs` >> gvs[ADD1])
  >> `LENGTH t.contexts < LENGTH s.contexts` by decide_tac
  >> drule_all step_pop_foreign >> strip_tac
  >> `LENGTH s.contexts = SUC (SUC (LENGTH rest))`
       by (qpat_assum `s.contexts = _` (once_rewrite_tac o single) >> simp[])
  >> `k ≤ LENGTH t.contexts ∧
      LENGTH s.contexts - k = SUC (LENGTH t.contexts - k)` by (gvs[] >> decide_tac)
  >> qpat_assum `s.contexts = _` (once_rewrite_tac o single)
  >> simp[ADD1]
QED

Theorem run_call_outer_msgParams:
  0 < k ∧ k < LENGTH e.contexts ∧ wf_state e ∧ run_call e = SOME (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (MAP (λp. (FST p).msgParams) t.contexts) =
  DROP (LENGTH e.contexts - k) (MAP (λp. (FST p).msgParams) e.contexts)
Proof
  strip_tac >> gvs[run_call_def]
  >> `(λp. wf_state (SND p) ∧ k ≤ LENGTH (SND p).contexts ∧
       DROP (LENGTH (SND p).contexts - k)
         (MAP (λp. (FST p).msgParams) (SND p).contexts) =
       DROP (LENGTH e.contexts - k) (MAP (λp. (FST p).msgParams) e.contexts)) (r,t)`
       suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[] >> rpt gen_tac >> strip_tac
  >> pairarg_tac >> gvs[]
  >> rename1 `LENGTH s.contexts ≥ LENGTH e.contexts`
  >> Cases_on `step s` >> gvs[]
  >> `k < LENGTH s.contexts` by decide_tac
  >> drule_all step_outer_msgParams >> strip_tac
  >> metis_tac[step_preserves_wf_state, SND]
QED

Theorem run_call_parent_msgParams:
  2 ≤ LENGTH e.contexts ∧ wf_state e ∧ run_call e = SOME (INL (),t) ⇒
  (FST (HD t.contexts)).msgParams = (FST (EL 1 e.contexts)).msgParams
Proof
  strip_tac
  >> `0 < LENGTH e.contexts - 1 ∧ LENGTH e.contexts - 1 < LENGTH e.contexts`
       by decide_tac
  >> `LENGTH e.contexts - 1 ≤ LENGTH t.contexts ∧
       DROP (LENGTH t.contexts - (LENGTH e.contexts - 1))
         (MAP (λp. (FST p).msgParams) t.contexts) =
       DROP (LENGTH e.contexts - (LENGTH e.contexts - 1))
         (MAP (λp. (FST p).msgParams) e.contexts)`
       by (irule run_call_outer_msgParams >> metis_tac[])
  >> `LENGTH t.contexts < LENGTH e.contexts`
       by (drule run_call_finite_trace >> simp[] >> strip_tac >> decide_tac)
  >> `LENGTH t.contexts = LENGTH e.contexts - 1 ∧
      LENGTH e.contexts - (LENGTH e.contexts - 1) = 1` by decide_tac
  >> gvs[]
  >> Cases_on `t.contexts` >> Cases_on `e.contexts` >> gvs[]
  >> rename1 `e.contexts = _::cs`
  >> Cases_on `cs` >> gvs[]
QED

Theorem run_call_reaches_trans:
  run_call_reaches es e ∧ LENGTH es.contexts ≤ LENGTH e.contexts ∧
  run_call_reaches e t ⇒ run_call_reaches es t
Proof
  simp[run_call_reaches_def] >> strip_tac
  >> irule RTC_TRANS >> qexists_tac `e` >> simp[]
  >> irule RTC_MONOTONE >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[] >> rpt strip_tac >> metis_tac[LESS_EQ_TRANS]
QED

Theorem run_call_step_equation:
  step e = (q,t) ⇒
  run_call e =
    OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
      (step o SND) (q,t)
Proof
  strip_tac >> simp[run_call_def, GREATER_EQ, Once OWHILE_THM]
QED

Theorem run_call_child_continuation:
  LENGTH e.contexts ≤ LENGTH c.contexts ∧
  run_call c = SOME (q,t) ⇒
  OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
    (step o SND) (INL (),c) =
  OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
    (step o SND) (q,t)
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac
  >> qmatch_goalsub_abbrev_tac `OWHILE G f _`
  >> `∀k. k < n ⇒ G (FUNPOW f k (INL (),c))`
       by (simp[Abbr `G`, Abbr `f`] >> rpt strip_tac >>
           first_x_assum drule >> pairarg_tac >> simp[] >>
           strip_tac >> decide_tac)
  >> `OWHILE G f (INL (),c) = OWHILE G f (FUNPOW f n (INL (),c))`
       by (irule OWHILE_trace_continuation >> qexists_tac `n` >> simp[])
  >> metis_tac[]
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
  strip_tac >> completeInduct_on `n` >> rpt gen_tac >> strip_tac
  >> Cases_on `n` >- gvs[]
  >> rename1 `FUNPOW (step o SND) (SUC j) _`
  >> `0 < LENGTH e.contexts` by (gvs[wf_state_def] >> Cases_on `e.contexts` >> gvs[])
  >> Cases_on `step e` >> rename1 `step e = (q,c)`
  >> `wf_state c` by metis_tac[step_preserves_wf_state, SND]
  >> `EVERY (λrb. P (lookup_account a rb.accounts))
        (active_rollbacks (LENGTH e.contexts) c)`
       by (irule step_foreign_account_invariant >> metis_tac[LESS_EQ_REFL])
  >> `P (lookup_account a e.rollback.accounts) ∧
      P (lookup_account a c.rollback.accounts)` by gvs[active_rollbacks_def]
  >> drule run_call_step_equation >> strip_tac
  >> Cases_on `q`
  >- suspend "continuing"
  >> gvs[Once OWHILE_THM]
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
  strip_tac
  >> Cases_on `(FST (HD es.contexts)).msgParams.callee = a`
  >- (qpat_x_assum `∀e r e'. _` irule >> qexistsl_tac [`es`,`r`] >> simp[])
  >> drule run_call_finite_trace >> strip_tac
  >> irule run_call_foreign_trace
  >> conj_tac >- metis_tac[]
  >> qexistsl_tac [`es`,`es`,`n`,`r`]
  >> simp[]
  >> conj_tac >- suspend "rely_push"
  >> irule active_rollbacks_initial >> simp[]
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
       by (qpat_assum `FST (HD c.contexts) = initial_context _ _ _ _ _`
             (once_rewrite_tac o single) >>
           simp[initial_context_def, initial_msg_params_def])
  >> qpat_x_assum `FST (HD c.contexts) = initial_context _ _ _ _ _` kall_tac
  >> irule run_call_static_frame >> gvs[] >> metis_tac[]
QED

Finalise run_call_account_frame

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
