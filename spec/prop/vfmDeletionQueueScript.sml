Theory vfmDeletionQueue
Ancestors
  arithmetic finite_map list num pair While
  vfmTypes vfmState vfmContext vfmExecution vfmExecutionProp
  vfmWfState vfmHandleStep vfmStaticCalls vfmStoragePredicates
  vfmAccountFrame vfmAccountDeletion vfmOriginalState vfmRunCall
  vfmRunWithinFrame vfmToDelete

(* A finite trace is unchanged up to deletion-queue erasure at every step. *)
Theorem step_funpow_toDelete:
  !n x y. FST x = FST y /\
    erase_toDelete (SND x) = erase_toDelete (SND y) ==>
    FST (FUNPOW (step o SND) n x) = FST (FUNPOW (step o SND) n y) /\
    erase_toDelete (SND (FUNPOW (step o SND) n x)) =
    erase_toDelete (SND (FUNPOW (step o SND) n y))
Proof
  Induct_on `n` >> simp[FUNPOW_SUC] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule step_toDelete >> simp[]
QED

(* Membership in an active deletion queue can only be introduced by
   SELFDESTRUCT executed as the account being added. *)
Theorem step_self_destruct_guarded_deletions[local]:
  s.contexts <> [] /\ ~MEM a s.rollback.toDelete /\
  ((FST (HD s.contexts)).msgParams.static \/
   (FST (HD s.contexts)).msgParams.callee <> a) /\
  step_self_destruct s = (r,t) ==>
  ~MEM a t.rollback.toDelete
Proof
  Cases_on `s.contexts` >>
  simp[step_self_destruct_def, bind_def, ignore_bind_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
    (cj 7 vfmStaticCallsTheory.cp_leaves)) >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
    (cj 13 vfmStaticCallsTheory.cp_leaves)) >>
  gvs[get_callee_def, get_current_context_def, bind_def, return_def,
      DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
    (cj 8 vfmStaticCallsTheory.cp_leaves)) >>
  gvs[get_accounts_def, bind_def, return_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
    (cj 5 vfmStaticCallsTheory.cp_leaves)) >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
    (cj 12 vfmStaticCallsTheory.cp_leaves)) >>
  gvs[update_accounts_def, get_original_def, bind_def, return_def,
      add_to_delete_def, finish_def, fail_def, DISJ_IMP_THM, FORALL_AND_THM,
      COND_RATOR, AllCaseEqs()] >>
  qpat_x_assum `assert_not_static _ = _` mp_tac >>
  simp[vfmStaticCallsTheory.assert_not_static_static]
QED

Theorem step_inst_guarded_deletion_projections[local]:
  s.contexts <> [] /\ ~MEM a s.rollback.toDelete /\
  ((FST (HD s.contexts)).msgParams.static \/
   (FST (HD s.contexts)).msgParams.callee <> a) /\
  step_inst op s = (r,t) ==>
  t.contexts <> [] /\ ~MEM a t.rollback.toDelete /\
  (MAP (\p. (SND p).toDelete) t.contexts =
     MAP (\p. (SND p).toDelete) s.contexts \/
   MAP (\p. (SND p).toDelete) t.contexts =
     s.rollback.toDelete :: MAP (\p. (SND p).toDelete) s.contexts)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `t.contexts <> []` by
    metis_tac[step_inst_preserves_nonempty_contexts, SND] >>
  Cases_on `op = SelfDestruct`
  >- (gvs[step_inst_def] >>
      `~MEM a t.rollback.toDelete` by
        metis_tac[step_self_destruct_guarded_deletions] >>
      drule_all (SRULE [vfmPreservesTheory.preserves_when_def]
        step_self_destruct_deletion_rel) >>
      disch_then (qspec_then `a` mp_tac) >>
      strip_tac >> gvs[]) >>
  Cases_on `op = Create \/ op = Create2`
  >- (gvs[step_inst_def] >>
      drule_all step_create_deletion_projections >> strip_tac >> gvs[]) >>
  Cases_on `op = Call \/ op = CallCode \/ op = DelegateCall \/ op = StaticCall`
  >- (gvs[step_inst_def] >>
      drule_all step_call_deletion_projections >> strip_tac >> gvs[]) >>
  gvs[] >> drule_all step_inst_deletion_exact >>
  simp[vfmPreservesTheory.preserves_when_def] >> disch_then drule_all >>
  strip_tac >> gvs[]
QED

Theorem step_inst_inc_pc_guarded_deletion_projections[local]:
  s.contexts <> [] /\ ~MEM a s.rollback.toDelete /\
  ((FST (HD s.contexts)).msgParams.static \/
   (FST (HD s.contexts)).msgParams.callee <> a) /\
  ignore_bind (step_inst op) (inc_pc_or_jump op) s = (r,t) ==>
  t.contexts <> [] /\ ~MEM a t.rollback.toDelete /\
  (MAP (\p. (SND p).toDelete) t.contexts =
     MAP (\p. (SND p).toDelete) s.contexts \/
   MAP (\p. (SND p).toDelete) t.contexts =
     s.rollback.toDelete :: MAP (\p. (SND p).toDelete) s.contexts)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `step_inst op s` >>
  rename1 `step_inst op s = (q,u)` >>
  drule_all step_inst_guarded_deletion_projections >> strip_tac >>
  (Cases_on `q`
  >- (rename1 `step_inst op s = (INL x,u)` >> Cases_on `x` >>
      `inc_pc_or_jump op u = (r,t)` by
        gvs[ignore_bind_def, bind_def] >>
      drule_all (SRULE [vfmPreservesTheory.preserves_when_def]
        inc_pc_or_jump_deletion_exact) >> strip_tac >>
      gvs[]) >>
  gvs[ignore_bind_def, bind_def])
QED

Theorem active_rollbacks_deletion_projection[local]:
  EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks d s) <=>
  ~MEM a s.rollback.toDelete /\
  EVERY (\q. ~MEM a q)
    (TAKE (SUC (LENGTH s.contexts) - MAX 2 d)
      (MAP (\p. (SND p).toDelete) s.contexts))
Proof
  simp[active_rollbacks_def, EVERY_MAP, GSYM MAP_TAKE,
       combinTheory.o_DEF]
QED

Theorem opcode_active_deletions[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks d s) /\
  ~MEM a t.rollback.toDelete /\
  (MAP (\p. (SND p).toDelete) t.contexts =
     MAP (\p. (SND p).toDelete) s.contexts \/
   MAP (\p. (SND p).toDelete) t.contexts =
     s.rollback.toDelete :: MAP (\p. (SND p).toDelete) s.contexts) ==>
  EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks d t)
Proof
  simp[active_rollbacks_deletion_projection] >> strip_tac >>
  qpat_assum `MAP _ t.contexts = _`
    (mp_tac o AP_TERM ``LENGTH : address list list -> num``) >>
  simp[] >> strip_tac >> gvs[] >>
  `SUC (SUC (LENGTH s.contexts)) - MAX 2 d =
   SUC (SUC (LENGTH s.contexts) - MAX 2 d)` by
    (simp[MAX_DEF] >> decide_tac) >>
  simp[]
QED

Theorem handle_step_active_deletions[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks d s) /\
  handle_step e s = (r,t) ==>
  EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks d t)
Proof
  strip_tac >> `s.contexts <> []` by (strip_tac >> gvs[]) >>
  drule_all handle_step_deletion_projections >> strip_tac >>
  gvs[active_rollbacks_deletion_projection] >>
  Cases_on `s.contexts` >> gvs[] >>
  `SUC (SUC (LENGTH t.contexts)) - MAX 2 d =
   SUC (SUC (LENGTH t.contexts) - MAX 2 d)` by
    (simp[MAX_DEF] >> decide_tac) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `TAKE n (_ :: _)` >>
  `0 < n` by (simp[Abbr `n`, MAX_DEF] >> decide_tac) >>
  Cases_on `n` >> gvs[]
QED

Theorem step_guarded_active_deletions[local]:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  ((FST (HD s.contexts)).msgParams.static \/
   (FST (HD s.contexts)).msgParams.callee <> a) /\
  EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks d s) /\
  step s = (r,t) ==>
  EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks d t)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  `~MEM a s.rollback.toDelete` by gvs[active_rollbacks_def] >>
  qpat_x_assum `step s = _` mp_tac >>
  rewrite_tac[step_def, handle_def] >>
  qpat_abbrev_tac `inner = bind get_current_context _` >>
  `!q u. inner s = (q,u) ==>
    d <= LENGTH u.contexts /\
    EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks d u)` by
    (simp[Abbr `inner`, bind_def, get_current_context_def, return_def] >>
     Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
       (FST (HD s.contexts)).pc` >> simp[]
     >- (IF_CASES_TAC >> rpt strip_tac >>
         drule_all step_inst_guarded_deletion_projections >> strip_tac >>
         qpat_assum `MAP _ u.contexts = _`
           (mp_tac o AP_TERM ``LENGTH : address list list -> num``) >>
         simp[] >> strip_tac >> gvs[] >>
         metis_tac[opcode_active_deletions]) >>
     rpt gen_tac >> strip_tac >>
     drule_all step_inst_inc_pc_guarded_deletion_projections >> strip_tac >>
     qpat_assum `MAP _ u.contexts = _`
       (mp_tac o AP_TERM ``LENGTH : address list list -> num``) >>
     simp[] >> strip_tac >> gvs[] >>
     metis_tac[opcode_active_deletions]) >>
  Cases_on `inner s` >> rename1 `inner s = (q,u)` >>
  `d <= LENGTH u.contexts /\
   EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks d u)` by metis_tac[] >>
  Cases_on `q` >> simp[] >>
  strip_tac >> drule_all handle_step_active_deletions >> simp[]
QED

Theorem step_foreign_active_deletions[local]:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  (FST (HD s.contexts)).msgParams.callee <> a /\
  EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks d s) /\
  step s = (r,t) ==>
  EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks d t)
Proof
  metis_tac[step_guarded_active_deletions]
QED

Theorem step_call_push_static[local]:
  step_call op s = (INL (),t) /\ s.contexts <> [] /\
  LENGTH s.contexts < LENGTH t.contexts /\
  (FST (HD s.contexts)).msgParams.static ==>
  (FST (HD t.contexts)).msgParams.static
Proof
  strip_tac >> drule_all step_call_reaches_proceed_call >> strip_tac
  >> drule_all call_prefix_contexts >> strip_tac
  >> drule_all proceed_call_inl_nonprecompile >> strip_tac
  >> drule_all proceed_call_nonprecompile_message >> strip_tac
  >> gvs[vfmStaticCallsTheory.cp_rel_def, initial_context_def, initial_msg_params_def]
QED

Theorem step_create_static_no_success[local]:
  s.contexts <> [] /\ (FST (HD s.contexts)).msgParams.static ==>
  step_create two s <> (INL (),t)
Proof
  strip_tac >> simp[step_create_def, bind_def, ignore_bind_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
       (cj 7 vfmStaticCallsTheory.cp_leaves))
  >> gvs[vfmStaticCallsTheory.cp_rel_def]
  >> imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
       (cj 4 vfmStaticCallsTheory.cp_memory))
  >> gvs[vfmStaticCallsTheory.cp_rel_def]
  >> imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
       (cj 5 vfmStaticCallsTheory.cp_leaves))
  >> gvs[vfmStaticCallsTheory.cp_rel_def]
  >> imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
       (cj 3 vfmStaticCallsTheory.cp_memory))
  >> gvs[vfmStaticCallsTheory.cp_rel_def]
  >> imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
       (cj 2 vfmStaticCallsTheory.cp_memory))
  >> gvs[vfmStaticCallsTheory.cp_rel_def]
  >> gvs[get_callee_def, get_accounts_def, get_gas_left_def,
         get_current_context_def, bind_def, return_def, AllCaseEqs()]
  >> imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
       (cj 4 vfmStaticCallsTheory.cp_leaves))
  >> gvs[vfmStaticCallsTheory.cp_rel_def]
  >> imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
       (cj 5 vfmStaticCallsTheory.cp_leaves))
  >> gvs[vfmStaticCallsTheory.cp_rel_def]
  >> qpat_x_assum `assert_not_static _ = _` mp_tac
  >> simp[vfmStaticCallsTheory.assert_not_static_static]
QED

Theorem step_push_static[local]:
  wf_state s /\ step s = (r,t) /\
  LENGTH s.contexts < LENGTH t.contexts /\
  (FST (HD s.contexts)).msgParams.static ==>
  (FST (HD t.contexts)).msgParams.static
Proof
  strip_tac >> drule_all step_grow_dispatch >> strip_tac
  >- (irule step_call_push_static >> metis_tac[wf_state_def])
  >> metis_tac[step_create_static_no_success, wf_state_def]
QED

Theorem step_active_static_prefix[local]:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (r,t) /\ d <= LENGTH t.contexts /\
  EVERY (\p. (FST p).msgParams.static)
    (TAKE (LENGTH s.contexts - d + 1) s.contexts) ==>
  EVERY (\p. (FST p).msgParams.static)
    (TAKE (LENGTH t.contexts - d + 1) t.contexts)
Proof
  strip_tac
  >> Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (drule_all step_same_frame_foreign >> strip_tac
      >> Cases_on `s.contexts` >> Cases_on `t.contexts`
      >> gvs[wf_state_def, TAKE_def])
  >> Cases_on `LENGTH t.contexts < LENGTH s.contexts`
  >- (drule_all step_pop_foreign >> strip_tac
      >> `d <= SUC (LENGTH rest)` by gvs[]
      >> qpat_x_assum `EVERY _ _` mp_tac
      >> qpat_x_assum `s.contexts = _` (fn th => once_rewrite_tac[th])
      >> simp[TAKE_def, arithmeticTheory.ADD1])
  >> `LENGTH s.contexts < LENGTH t.contexts` by decide_tac
  >> drule_all step_push_foreign >> strip_tac
  >> `(FST (HD s.contexts)).msgParams.static` by
       (Cases_on `s.contexts` >> gvs[TAKE_def])
  >> drule_all step_push_static >> strip_tac
  >> namedCases_on `s.contexts` ["", "caller oldtail"] >- gvs[wf_state_def]
  >> namedCases_on `t.contexts` ["", "child parents"] >- gvs[]
  >> Cases_on `parents` >- gvs[]
  >> gvs[TAKE_def, arithmeticTheory.ADD1]
  >> qpat_x_assum `MAP FST _ = _`
       (mp_tac o Q.AP_TERM
         `\xs. EVERY (\q. q.msgParams.static) (TAKE (LENGTH oldtail + 1 - d) xs)`)
  >> simp[GSYM MAP_TAKE, EVERY_MAP, combinTheory.o_DEF]
QED

Theorem run_call_static_deletion_exclusion:
  wf_state es /\ (FST (HD es.contexts)).msgParams.static /\
  EVERY (\rb. ~MEM a rb.toDelete) (active_rollbacks (LENGTH es.contexts) es) /\
  run_call es = SOME (r,t) ==>
  ~MEM a t.rollback.toDelete
Proof
  strip_tac
  >> `0 < LENGTH es.contexts` by (Cases_on `es.contexts` >> gvs[wf_state_def])
  >> gvs[run_call_def]
  >> `((\p. wf_state (SND p) /\
       EVERY (\rb. ~MEM a rb.toDelete)
         (active_rollbacks (LENGTH es.contexts) (SND p)) /\
       (LENGTH es.contexts <= LENGTH (SND p).contexts ==>
        EVERY (\c. (FST c).msgParams.static)
          (TAKE (LENGTH (SND p).contexts - LENGTH es.contexts + 1)
            (SND p).contexts))) (r,t))`
     suffices_by simp[active_rollbacks_def]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[] >> conj_tac
  >- (Cases_on `es.contexts` >> gvs[])
  >> rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac
  >> Cases_on `step s''` >> rename1 `step s'' = (v,u)` >> gvs[]
  >> `LENGTH es.contexts <= LENGTH s''.contexts` by decide_tac
  >> `EVERY (\c. (FST c).msgParams.static)
       (TAKE (LENGTH s''.contexts - LENGTH es.contexts + 1) s''.contexts)`
       by simp[]
  >> `(FST (HD s''.contexts)).msgParams.static` by
       (Cases_on `s''.contexts` >> gvs[TAKE_def])
  >> conj_tac
  >- (qspec_then `s''` mp_tac (GEN_ALL step_preserves_wf_state) >> simp[])
  >> conj_tac
  >- (irule step_guarded_active_deletions >> metis_tac[])
  >> strip_tac >> drule_all step_active_static_prefix >> simp[]
QED

Theorem step_foreign_active_balance_deletions[local]:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  (FST (HD s.contexts)).msgParams.callee <> a /\
  (!acc acc'. P acc /\ foreign_balance_change acc acc' ==> P acc') /\
  EVERY (\rb. P (lookup_account a rb.accounts) /\ ~MEM a rb.toDelete)
    (active_rollbacks d s) /\ step s = (r,t) ==>
  EVERY (\rb. P (lookup_account a rb.accounts) /\ ~MEM a rb.toDelete)
    (active_rollbacks d t)
Proof
  simp[EVERY_CONJ] >> strip_tac >> conj_tac
  >- (drule_all step_foreign_balance_invariant >> simp[]) >>
  drule_all step_foreign_active_deletions >> simp[]
QED

Theorem run_call_foreign_active_trace[local]:
  (!d s q t. 0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
     (FST (HD s.contexts)).msgParams.callee <> a /\
     EVERY Q (active_rollbacks d s) /\ step s = (q,t) ==>
     EVERY Q (active_rollbacks d t)) /\
  (!s c q t.
     run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts /\
     wf_state s /\ (FST (HD s.contexts)).msgParams.callee <> a /\
     Q s.rollback /\ Q c.rollback /\
     (2 <= LENGTH c.contexts ==> Q (SND (HD c.contexts))) /\
     step s = (INL (),c) /\ LENGTH s.contexts < LENGTH c.contexts /\
     (FST (HD c.contexts)).msgParams.callee = a /\
     run_call c = SOME (q,t) ==> Q t.rollback) ==>
  !n e r t.
    ~(\(q,s). ISL q /\ LENGTH e.contexts <= LENGTH s.contexts)
       (FUNPOW (step o SND) n (INL (),e)) /\
    run_call_reaches es e /\ LENGTH es.contexts <= LENGTH e.contexts /\
    wf_state e /\ (FST (HD e.contexts)).msgParams.callee <> a /\
    EVERY Q (active_rollbacks (LENGTH e.contexts) e) /\
    run_call e = SOME (r,t) ==> Q t.rollback
Proof
  strip_tac >> completeInduct_on `n` >> rpt gen_tac >> strip_tac
  >> Cases_on `n` >- gvs[]
  >> rename1 `FUNPOW (step o SND) (SUC j) _`
  >> `0 < LENGTH e.contexts` by (gvs[wf_state_def] >> Cases_on `e.contexts` >> gvs[])
  >> Cases_on `step e` >> rename1 `step e = (q,c)`
  >> `wf_state c` by metis_tac[step_preserves_wf_state, SND]
  >> `EVERY Q (active_rollbacks (LENGTH e.contexts) c)`
       by (first_x_assum irule >> metis_tac[LESS_EQ_REFL])
  >> `Q e.rollback /\ Q c.rollback` by
       (conj_tac
        >- (qpat_x_assum `EVERY _ (active_rollbacks _ e)` mp_tac >> simp[active_rollbacks_def])
        >> qpat_x_assum `EVERY _ (active_rollbacks _ c)` mp_tac >> simp[active_rollbacks_def])
  >> drule run_call_step_equation >> strip_tac
  >> Cases_on `q`
  >- suspend "continuing"
  >> gvs[Once OWHILE_THM]
QED

Resume run_call_foreign_active_trace[continuing]:
  Cases_on `x` >> gvs[]
  >> Cases_on `LENGTH c.contexts < LENGTH e.contexts`
  >- gvs[Once OWHILE_THM]
  >> Cases_on `LENGTH c.contexts = LENGTH e.contexts`
  >- suspend "same_depth"
  >> suspend "push"
QED

Resume run_call_foreign_active_trace[same_depth]:
  `run_call_reaches es c` by (irule run_call_reaches_step >> metis_tac[])
  >> `(FST (HD c.contexts)).msgParams.callee <> a`
       by (drule_all step_same_frame_foreign >> metis_tac[])
  >> `run_call c = SOME (r,t)` by gvs[run_call_def, GREATER_EQ]
  >> qpat_x_assum `!m. m < SUC j ==> _` (qspec_then `j` mp_tac)
  >> simp[] >> disch_then irule
  >> qexists_tac `c` >> qexists_tac `r`
  >> gvs[FUNPOW, combinTheory.o_DEF]
QED

Resume run_call_foreign_active_trace[push]:
  `LENGTH e.contexts < LENGTH c.contexts` by decide_tac
  >> `run_call_reaches es c` by (irule run_call_reaches_step >> metis_tac[])
  >> qpat_x_assum `~(\(q,s). _) _` mp_tac
  >> simp[Once FUNPOW] >> strip_tac
  >> drule_at (Pat `~ _`) run_call_nested_trace
  >> simp[] >> strip_tac
  >> rename1 `m <= j`
  >> Cases_on `FUNPOW (step o SND) m (INL (),c)`
  >> rename1 `run_call c = SOME (q,v)`
  >> `Q (SND (HD c.contexts))` by
       (drule_all step_push_foreign >> strip_tac
        >> `TL (active_rollbacks (LENGTH e.contexts) c) =
             SND (HD c.contexts) :: TL (active_rollbacks (LENGTH e.contexts) e)`
             by (irule active_rollbacks_push_tail >> simp[])
        >> qpat_x_assum `!d s q t. _` kall_tac
        >> qpat_x_assum `!s c q t. _` kall_tac
        >> qpat_x_assum `!m. _` kall_tac
        >> Cases_on `active_rollbacks (LENGTH e.contexts) c` >> gvs[])
  >> `Q v.rollback` by
       (Cases_on `(FST (HD c.contexts)).msgParams.callee = a`
        >- (qpat_x_assum `!s c q t. _` irule >>
            qexistsl_tac [`c`,`q`,`e`] >> simp[])
        >> qpat_x_assum `!m. m < SUC j ==> _` (qspec_then `m` mp_tac)
        >> simp[] >> disch_then irule
        >> qexists_tac `c` >> qexists_tac `q` >> simp[]
        >> irule active_rollbacks_initial >> simp[])
  >> `OWHILE (\(r,s). ISL r /\ LENGTH e.contexts <= LENGTH s.contexts)
        (step o SND) (INL (),c) =
      OWHILE (\(r,s). ISL r /\ LENGTH e.contexts <= LENGTH s.contexts)
        (step o SND) (q,v)`
       by (irule run_call_child_continuation >> simp[])
  >> Cases_on `q`
  >- suspend "child_return"
  >> gvs[Once OWHILE_THM]
QED

Resume run_call_foreign_active_trace[child_return]:
  Cases_on `x` >> gvs[]
  >> drule_all step_push_foreign >> strip_tac
  >> `LENGTH e.contexts <= LENGTH v.contexts`
       by (qpat_assum `run_call c = _`
             (mp_then Any mp_tac (Q.INST
               [`d` |-> `LENGTH e.contexts`, `k` |-> `LENGTH e.contexts`]
               (Q.INST [`e` |-> `c`] run_call_outer_saved_rollbacks))) >> simp[])
  >> `LENGTH v.contexts = LENGTH e.contexts` by decide_tac
  >> `wf_state v` by metis_tac[run_call_preserves_wf_state]
  >> `2 <= LENGTH c.contexts` by decide_tac
  >> `(FST (HD v.contexts)).msgParams = (FST (HD e.contexts)).msgParams`
       by (drule_all run_call_parent_msgParams >> simp[])
  >> `EVERY Q (active_rollbacks (LENGTH e.contexts) v)`
       by (irule run_call_saved_account_invariant >> simp[] >>
           qexists_tac `c` >> simp[] >>
           qpat_x_assum `EVERY _ (active_rollbacks _ c)` mp_tac >>
           simp[active_rollbacks_def])
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
  >> qpat_x_assum `!m. m < SUC j ==> _` (qspec_then `j-m` mp_tac)
  >> simp[] >> disch_then irule
  >> qexistsl_tac [`v`,`r`] >> simp[] >> metis_tac[]
QED

Finalise run_call_foreign_active_trace[local]

Theorem run_call_foreign_active_invariant[local]:
  (!d s q t. 0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
     (FST (HD s.contexts)).msgParams.callee <> a /\
     EVERY Q (active_rollbacks d s) /\ step s = (q,t) ==>
     EVERY Q (active_rollbacks d t)) /\
  (!s c q t.
     run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts /\
     wf_state s /\ (FST (HD s.contexts)).msgParams.callee <> a /\
     Q s.rollback /\ Q c.rollback /\
     (2 <= LENGTH c.contexts ==> Q (SND (HD c.contexts))) /\
     step s = (INL (),c) /\ LENGTH s.contexts < LENGTH c.contexts /\
     (FST (HD c.contexts)).msgParams.callee = a /\
     run_call c = SOME (q,t) ==> Q t.rollback) /\
  wf_state es /\ (FST (HD es.contexts)).msgParams.callee <> a /\
  Q es.rollback /\
  (2 <= LENGTH es.contexts ==> Q (SND (HD es.contexts))) /\
  run_call es = SOME (r,t) ==> Q t.rollback
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >>
  irule run_call_foreign_active_trace >>
  qexistsl_tac [`a`,`es`,`es`,`n`,`r`] >> simp[] >>
  metis_tac[active_rollbacks_initial]
QED

Theorem run_call_foreign_balance_deletions:
  (!acc acc'. P acc /\ foreign_balance_change acc acc' ==> P acc') /\
  (!s c q u.
     run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts /\
     wf_state s /\ (FST (HD s.contexts)).msgParams.callee <> a /\
     (P (lookup_account a s.rollback.accounts) /\ ~MEM a s.rollback.toDelete) /\
     (P (lookup_account a c.rollback.accounts) /\ ~MEM a c.rollback.toDelete) /\
     (2 <= LENGTH c.contexts ==>
       P (lookup_account a (SND (HD c.contexts)).accounts) /\
       ~MEM a (SND (HD c.contexts)).toDelete) /\
     step s = (INL (),c) /\ LENGTH s.contexts < LENGTH c.contexts /\
     (FST (HD c.contexts)).msgParams.callee = a /\
     run_call c = SOME (q,u) ==>
       P (lookup_account a u.rollback.accounts) /\ ~MEM a u.rollback.toDelete) /\
  wf_state es /\ (FST (HD es.contexts)).msgParams.callee <> a /\
  EVERY (\rb. P (lookup_account a rb.accounts) /\ ~MEM a rb.toDelete)
    (active_rollbacks (LENGTH es.contexts) es) /\
  run_call es = SOME (r,t) ==>
  P (lookup_account a t.rollback.accounts) /\ ~MEM a t.rollback.toDelete
Proof
  strip_tac >> irule (BETA_RULE (Q.INST
    [`Q` |-> `\rb. P (lookup_account a rb.accounts) /\ ~MEM a rb.toDelete`]
    run_call_foreign_active_invariant))
  >> conj_tac
  >- (rpt strip_tac >> drule_all step_foreign_active_balance_deletions >> simp[])
  >> qexistsl_tac [`es`,`r`] >> simp[]
  >> `P (lookup_account a es.rollback.accounts) /\ ~MEM a es.rollback.toDelete`
       by gvs[active_rollbacks_def]
  >> simp[] >> conj_tac >- metis_tac[]
  >> strip_tac
  >> mp_tac (Q.INST [`d` |-> `LENGTH es.contexts`, `s` |-> `es`]
       active_rollbacks_pop_sources)
  >> simp[] >> gvs[EVERY_MEM]
QED

(* Relate the live and saved queues in executions that differ only by
   an entry suffix. Only rollbacks the current call can restore matter. *)
Theorem active_deletion_queues_head:
  HD (MAP (\rb. rb.toDelete) (active_rollbacks d s)) = s.rollback.toDelete
Proof
  simp[active_rollbacks_def]
QED

Theorem active_deletion_queues_initial[local]:
  s.contexts <> [] ==>
  MAP (\rb. rb.toDelete) (active_rollbacks (LENGTH s.contexts) s) =
    s.rollback.toDelete ::
      (if 2 <= LENGTH s.contexts then [(SND (HD s.contexts)).toDelete] else [])
Proof
  Cases_on `s.contexts` >> simp[active_rollbacks_def] >>
  Cases_on `t` >> simp[MAX_DEF]
QED

Theorem active_deletion_queues_exact[local]:
  t.rollback.toDelete = s.rollback.toDelete /\
  MAP (\p. (SND p).toDelete) t.contexts =
    MAP (\p. (SND p).toDelete) s.contexts ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    MAP (\rb. rb.toDelete) (active_rollbacks d s)
Proof
  strip_tac >>
  `LENGTH t.contexts = LENGTH s.contexts` by metis_tac[LENGTH_MAP] >>
  simp[active_rollbacks_def, MAP_MAP_o, combinTheory.o_DEF] >>
  rewrite_tac[MAP_TAKE] >> simp[]
QED

Theorem active_deletion_queues_saved_push[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  t.rollback.toDelete = s.rollback.toDelete /\
  MAP (\p. (SND p).toDelete) t.contexts =
    s.rollback.toDelete :: MAP (\p. (SND p).toDelete) s.contexts ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    HD (MAP (\rb. rb.toDelete) (active_rollbacks d s)) ::
    MAP (\rb. rb.toDelete) (active_rollbacks d s)
Proof
  strip_tac >>
  `LENGTH t.contexts = SUC (LENGTH s.contexts)` by metis_tac[LENGTH_MAP, LENGTH] >>
  `SUC (SUC (LENGTH s.contexts)) - MAX 2 d =
   SUC (SUC (LENGTH s.contexts) - MAX 2 d)` by
    (simp[MAX_DEF] >> decide_tac) >>
  simp[active_rollbacks_def, MAP_MAP_o, combinTheory.o_DEF] >>
  rewrite_tac[MAP_TAKE] >> simp[]
QED

Theorem active_deletion_queues_same_or_push[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  t.rollback.toDelete = s.rollback.toDelete /\
  (MAP (\p. (SND p).toDelete) t.contexts =
     MAP (\p. (SND p).toDelete) s.contexts \/
   MAP (\p. (SND p).toDelete) t.contexts =
     s.rollback.toDelete :: MAP (\p. (SND p).toDelete) s.contexts) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    if LENGTH t.contexts = LENGTH s.contexts then
      MAP (\rb. rb.toDelete) (active_rollbacks d s)
    else HD (MAP (\rb. rb.toDelete) (active_rollbacks d s)) ::
      MAP (\rb. rb.toDelete) (active_rollbacks d s)
Proof
  strip_tac
  >- (`LENGTH t.contexts = LENGTH s.contexts` by metis_tac[LENGTH_MAP] >>
      simp[] >> irule active_deletion_queues_exact >> simp[]) >>
  `LENGTH t.contexts = SUC (LENGTH s.contexts)` by metis_tac[LENGTH_MAP, LENGTH] >>
  simp[] >> irule active_deletion_queues_saved_push >> simp[]
QED

Theorem handle_exception_deletion_selector[local]:
  s.contexts = (callee,rb)::parent::rest /\
  handle_exception e s = (r,t) ==>
  t.rollback.toDelete =
    (if e <> NONE /\
       (if e = SOME Reverted then
          callee.msgParams.gasLimit - callee.gasUsed <= (FST parent).gasUsed
        else callee.gasUsed <= callee.msgParams.gasLimit)
    then rb.toDelete else s.rollback.toDelete) /\
  MAP (\p. (SND p).toDelete) t.contexts =
    if e <> NONE /\ e <> SOME Reverted /\
       ~(callee.gasUsed <= callee.msgParams.gasLimit)
    then MAP (\p. (SND p).toDelete) s.contexts
    else TL (MAP (\p. (SND p).toDelete) s.contexts)
Proof
  strip_tac >> Cases_on `parent` >>
  Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  gvs[handle_exception_def, bind_def, ignore_bind_def,
      get_gas_left_def, get_current_context_def, return_def,
      consume_gas_def, set_return_data_def, set_current_context_def,
      get_num_contexts_def, get_return_data_def, get_output_to_def,
      reraise_def, assert_def, fail_def,
      inc_pc_def, push_stack_def, write_memory_def,
      pop_and_incorporate_context_def, pop_context_def,
      set_rollback_def, unuse_gas_def,
      update_gas_refund_def, push_logs_def, AllCaseEqs()] >>
  Cases_on `callee.msgParams.outputTo` >>
  gvs[bind_def, ignore_bind_def, get_current_context_def,
      set_current_context_def, assert_def, fail_def, return_def, AllCaseEqs()]
QED

Theorem active_deletion_queues_saved_pop[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  s.contexts = h::parent::rest /\
  MAP (\p. (SND p).toDelete) t.contexts =
    TL (MAP (\p. (SND p).toDelete) s.contexts) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    t.rollback.toDelete ::
    TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
Proof
  strip_tac >>
  `LENGTH t.contexts = SUC (LENGTH rest)` by
    (qpat_x_assum `MAP _ t.contexts = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[]) >>
  `SUC (SUC (SUC (LENGTH rest))) - MAX 2 d =
   SUC (SUC (SUC (LENGTH rest)) - MAX 2 d)` by
    (gvs[MAX_DEF] >> decide_tac) >>
  gvs[active_rollbacks_def, MAP_MAP_o, combinTheory.o_DEF] >>
  rewrite_tac[MAP_TAKE] >> simp[]
QED

Theorem active_deletion_queues_saved_exact[local]:
  MAP (\p. (SND p).toDelete) t.contexts =
    MAP (\p. (SND p).toDelete) s.contexts ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    t.rollback.toDelete ::
    TL (MAP (\rb. rb.toDelete) (active_rollbacks d s))
Proof
  strip_tac >>
  `LENGTH t.contexts = LENGTH s.contexts` by metis_tac[LENGTH_MAP] >>
  simp[active_rollbacks_def, MAP_MAP_o, combinTheory.o_DEF] >>
  rewrite_tac[MAP_TAKE] >> simp[]
QED

Theorem handle_exception_queue_selector[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  s.contexts = (callee,rb)::parent::rest /\
  handle_exception e s = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    (if e <> NONE /\
        (if e = SOME Reverted then
           callee.msgParams.gasLimit - callee.gasUsed <= (FST parent).gasUsed
         else callee.gasUsed <= callee.msgParams.gasLimit)
     then HD (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
     else s.rollback.toDelete) ::
    (if e <> NONE /\ e <> SOME Reverted /\
        ~(callee.gasUsed <= callee.msgParams.gasLimit)
     then TL (MAP (\rb. rb.toDelete) (active_rollbacks d s))
     else TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s))))
Proof
  strip_tac >>
  `HD (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s))) =
   rb.toDelete` by
    (`SUC (SUC (SUC (LENGTH rest))) - MAX 2 d =
      SUC (SUC (SUC (LENGTH rest)) - MAX 2 d)` by
       (gvs[MAX_DEF] >> decide_tac) >>
     simp[active_rollbacks_def]) >>
  drule_all handle_exception_deletion_selector >> strip_tac >>
  Cases_on `e <> NONE /\ e <> SOME Reverted /\
            ~(callee.gasUsed <= callee.msgParams.gasLimit)`
  >- (`MAP (\p. (SND p).toDelete) t.contexts =
       MAP (\p. (SND p).toDelete) s.contexts` by gvs[] >>
      drule active_deletion_queues_saved_exact >>
      disch_then (qspec_then `d` mp_tac) >> gvs[]) >>
  `MAP (\rb. rb.toDelete) (active_rollbacks d t) =
   t.rollback.toDelete ::
   TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))` by
    (irule active_deletion_queues_saved_pop >> simp[] >> metis_tac[]) >>
  gvs[] >> IF_CASES_TAC >> gvs[]
QED

Theorem handle_exception_queue_suffix[local]:
  0 < d /\ d <= LENGTH s.contexts /\ s.contexts <> [] /\
  MAP FST s.contexts = MAP FST u.contexts /\
  MAP (\rb. rb.toDelete) (active_rollbacks d s) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d u)) /\
  handle_exception e s = (r,t) /\ handle_exception e u = (q,v) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d v))
Proof
  reverse (Cases_on `2 <= LENGTH s.contexts`)
  >- (rpt strip_tac >>
      `LENGTH s.contexts = LENGTH u.contexts` by metis_tac[LENGTH_MAP] >>
      `u.contexts <> [] /\ ~(2 <= LENGTH u.contexts)` by
        (gvs[] >> metis_tac[LENGTH_NIL]) >>
      imp_res_tac handle_exception_deletion_projections >> gvs[] >>
      `MAP (\rb. rb.toDelete) (active_rollbacks d t) =
       MAP (\rb. rb.toDelete) (active_rollbacks d s)` by
        (irule active_deletion_queues_exact >> simp[]) >>
      `MAP (\rb. rb.toDelete) (active_rollbacks d v) =
       MAP (\rb. rb.toDelete) (active_rollbacks d u)` by
        (irule active_deletion_queues_exact >> simp[]) >>
      metis_tac[]) >>
  Cases_on `s.contexts` >> simp[] >>
  rename1 `s.contexts = sh::st` >> Cases_on `st` >> simp[] >>
  Cases_on `u.contexts` >> simp[] >>
  rename1 `u.contexts = uh::ut` >> Cases_on `ut` >> simp[] >>
  PairCases_on `sh` >> PairCases_on `uh` >>
  rpt strip_tac >> gvs[rollback_state_component_equality] >>
  PairCases_on `h` >> PairCases_on `h'` >> gvs[] >>
  `d <= LENGTH u.contexts /\ d <= LENGTH s.contexts` by
    (simp[] >> metis_tac[LENGTH_MAP]) >>
  `s.rollback.toDelete = u.rollback.toDelete ++ b` by
    (qpat_x_assum `MAP _ (active_rollbacks d s) = _`
       (mp_tac o Q.AP_TERM `HD`) >> simp[active_rollbacks_def]) >>
  qpat_x_assum `handle_exception e s = _` mp_tac >>
  drule_all handle_exception_queue_selector >> strip_tac >> disch_tac >>
  qpat_x_assum `handle_exception e u = _` kall_tac >>
  drule_all handle_exception_queue_selector >> strip_tac >>
  gvs[] >>
  `SUC (SUC (SUC (LENGTH t''))) - MAX 2 d =
   SUC (SUC (SUC (LENGTH t'')) - MAX 2 d)` by
    (gvs[MAX_DEF] >> decide_tac) >>
  rpt IF_CASES_TAC >>
  simp[MAP_TL, active_rollbacks_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem handle_create_control[local]:
  s.contexts = (c,rb)::rest /\ handle_create e s = (r,t) ==>
  r = INR
    (case (e,c.msgParams.outputTo) of
       (NONE,Code address) =>
         if ~(case c.returnData of h::_ => h <> n2w 0xef | _ => T)
         then SOME InvalidContractPrefix
         else if c.gasUsed + code_deposit_cost * LENGTH c.returnData >
                 c.msgParams.gasLimit \/ LENGTH c.returnData > max_code_size
         then SOME OutOfGas else NONE
     | _ => e) /\
  FST (HD t.contexts) = c with gasUsed := c.gasUsed +
    (if e = NONE /\ (?address. c.msgParams.outputTo = Code address) /\
        (case c.returnData of h::_ => h <> n2w 0xef | _ => T) /\
        c.gasUsed + code_deposit_cost * LENGTH c.returnData <= c.msgParams.gasLimit
     then code_deposit_cost * LENGTH c.returnData else 0)
Proof
  strip_tac >> Cases_on `e` >> Cases_on `c.msgParams.outputTo` >>
  gvs[handle_create_def, get_return_data_def, get_output_to_def,
      get_current_context_def, bind_def, ignore_bind_def, return_def,
      assert_def, fail_def, consume_gas_def, set_current_context_def,
      update_accounts_def, reraise_def, AllCaseEqs()] >>
  Cases_on `c.returnData` >> gvs[AllCaseEqs()]
QED

Theorem handle_create_control_queue_suffix[local]:
  s.contexts <> [] /\ MAP FST s.contexts = MAP FST u.contexts /\
  MAP (\rb. rb.toDelete) (active_rollbacks d s) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d u)) /\
  handle_create e s = (r,t) /\ handle_create e u = (q,v) ==>
  r = q /\ MAP FST t.contexts = MAP FST v.contexts /\
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d v))
Proof
  Cases_on `s.contexts` >> simp[] >> Cases_on `u.contexts` >> simp[] >>
  PairCases_on `h` >> PairCases_on `h'` >> strip_tac >> gvs[] >>
  imp_res_tac handle_create_control >>
  imp_res_tac handle_create_preserves_tl_and_snd_hd >>
  imp_res_tac (SRULE [vfmPreservesTheory.preserves_when_def]
                handle_create_deletion_exact) >>
  gvs[] >> reverse conj_tac
  >- (`MAP (\rb. rb.toDelete) (active_rollbacks d t) =
       MAP (\rb. rb.toDelete) (active_rollbacks d s)` by
        (irule active_deletion_queues_exact >> simp[]) >>
      `MAP (\rb. rb.toDelete) (active_rollbacks d v) =
       MAP (\rb. rb.toDelete) (active_rollbacks d u)` by
        (irule active_deletion_queues_exact >> simp[]) >>
      metis_tac[]) >>
  Cases_on `t.contexts` >> Cases_on `v.contexts` >> gvs[]
QED

Theorem handle_step_queue_suffix[local]:
  0 < d /\ d <= LENGTH s.contexts /\ s.contexts <> [] /\
  MAP FST s.contexts = MAP FST u.contexts /\
  MAP (\rb. rb.toDelete) (active_rollbacks d s) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d u)) /\
  handle_step e s = (r,t) /\ handle_step e u = (q,v) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d v))
Proof
  strip_tac >> Cases_on `vfm_abort e`
  >- gvs[handle_step_def, reraise_def] >>
  `?ce cs. handle_create e s = (INR ce : unit + vfmExecution$exception option,cs)` by
    metis_tac[handle_create_INR] >>
  `?ue us. handle_create e u = (INR ue : unit + vfmExecution$exception option,us)` by
    metis_tac[handle_create_INR] >>
  drule_all handle_create_control_queue_suffix >> strip_tac >>
  imp_res_tac handle_create_preserves_length >>
  `cs.contexts <> [] /\ d <= LENGTH cs.contexts` by
    (gvs[] >> metis_tac[LENGTH_NIL]) >>
  gvs[handle_step_def, handle_def] >>
  `d <= LENGTH cs.contexts` by simp[] >>
  drule_all handle_exception_queue_suffix >> simp[]
QED

Theorem step_self_destruct_deletion_selector[local]:
  s.contexts <> [] /\ step_self_destruct s = (r,t) ==>
  t.rollback.toDelete =
    if r = INR NONE /\
       account_empty (lookup_account (FST (HD s.contexts)).msgParams.callee
                        s.originalAccounts)
    then (FST (HD s.contexts)).msgParams.callee :: s.rollback.toDelete
    else s.rollback.toDelete
Proof
  Cases_on `s.contexts` >> simp[] >>
  simp[step_self_destruct_def, bind_def, ignore_bind_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
    (cj 7 vfmStaticCallsTheory.cp_leaves)) >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
    (cj 13 vfmStaticCallsTheory.cp_leaves)) >>
  gvs[get_callee_def, get_current_context_def, bind_def, return_def,
      DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
    (cj 8 vfmStaticCallsTheory.cp_leaves)) >>
  gvs[get_accounts_def, bind_def, return_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
    (cj 5 vfmStaticCallsTheory.cp_leaves)) >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac (PURE_REWRITE_RULE [vfmStaticCallsTheory.cp_def]
    (cj 12 vfmStaticCallsTheory.cp_leaves)) >>
  gvs[update_accounts_def, get_original_def, bind_def, return_def,
      add_to_delete_def, finish_def, fail_def, DISJ_IMP_THM, FORALL_AND_THM,
      COND_RATOR, AllCaseEqs()] >>
  gvs[assert_not_static_def, get_static_def, pop_stack_def, access_address_def,
      consume_gas_def, set_return_data_def, bind_def, ignore_bind_def,
      get_current_context_def, set_current_context_def, return_def,
      assert_def, fail_def, AllCaseEqs()] >>
  gvs[domain_check_def, set_domain_def, ignore_bind_def, bind_def,
      return_def, fail_def, AllCaseEqs()]
QED

Theorem step_self_destruct_finishes[local]:
  s.contexts = (c,rb)::rest ==>
  (FST (step_self_destruct s) = INR NONE <=>
   1 <= LENGTH c.stack /\
   (case s.msdomain of Collect d => T
    | Enforce d => fIN (w2w (HD c.stack)) d.addresses) /\
   c.gasUsed +
     (static_gas SelfDestruct +
      zero_warm (if fIN (w2w (HD c.stack)) s.rollback.accesses.addresses
                 then warm_access_cost else cold_access_cost) +
      (if 0 < (lookup_account c.msgParams.callee s.rollback.accounts).balance /\
          account_empty (lookup_account (w2w (HD c.stack)) s.rollback.accounts)
       then self_destruct_new_account_cost else 0)) <= c.msgParams.gasLimit /\
   ~c.msgParams.static)
Proof
  strip_tac >> Cases_on `1 <= LENGTH c.stack` >>
  simp[step_self_destruct_def, pop_stack_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, fail_def] >>
  Cases_on `s.msdomain` >>
  simp[access_address_def, domain_check_def, set_domain_def, bind_def,
       ignore_bind_def, return_def, fail_def] >>
  simp[HD_TAKE] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[get_callee_def, get_current_context_def, set_return_data_def,
       set_current_context_def, get_accounts_def, bind_def, ignore_bind_def,
       return_def, consume_gas_def, assert_def, fail_def] >>
  IF_CASES_TAC >> simp[] >>
  simp[assert_not_static_def, get_static_def, get_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  Cases_on `c.msgParams.static` >> simp[] >>
  simp[update_accounts_def, get_original_def, bind_def, ignore_bind_def,
       return_def, add_to_delete_def, finish_def, COND_RATOR] >>
  IF_CASES_TAC >> simp[bind_def, ignore_bind_def, return_def,
                      update_accounts_def, add_to_delete_def, finish_def]
QED

Theorem step_self_destruct_queue_selector[local]:
  s.contexts <> [] /\ step_self_destruct s = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    (if r = INR NONE /\
        account_empty (lookup_account (FST (HD s.contexts)).msgParams.callee
                         s.originalAccounts)
     then (FST (HD s.contexts)).msgParams.callee :: s.rollback.toDelete
     else s.rollback.toDelete) ::
    TL (MAP (\rb. rb.toDelete) (active_rollbacks d s))
Proof
  strip_tac >> drule_all step_self_destruct_deletion_provenance >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  drule_all step_self_destruct_deletion_selector >> strip_tac >>
  drule active_deletion_queues_saved_exact >>
  disch_then (qspec_then `d` mp_tac) >> simp[]
QED

Theorem step_self_destruct_handler_control[local]:
  s.contexts <> [] /\
  step_self_destruct s = ((INR e : unit + vfmExecution$exception option),ss) ==>
  e <> SOME Reverted /\
  (e = NONE ==> (FST (HD ss.contexts)).returnData = [] /\
    (FST (HD ss.contexts)).gasUsed <=
      (FST (HD ss.contexts)).msgParams.gasLimit)
Proof
  strip_tac >> qpat_x_assum `step_self_destruct s = _` mp_tac >>
  Cases_on `1 <= LENGTH (FST (HD s.contexts)).stack` >>
  simp[step_self_destruct_def, pop_stack_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, fail_def] >>
  Cases_on `s.msdomain` >>
  simp[access_address_def, domain_check_def, set_domain_def, bind_def,
       ignore_bind_def, return_def, fail_def, HD_TAKE] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[get_callee_def, get_current_context_def, set_return_data_def,
       set_current_context_def, get_accounts_def, bind_def, ignore_bind_def,
       return_def, consume_gas_def, assert_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[]) >>
  simp[assert_not_static_def, get_static_def, get_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[]) >>
  simp[update_accounts_def, get_original_def, bind_def, ignore_bind_def,
       return_def, add_to_delete_def, finish_def, COND_RATOR] >>
  rpt (COND_CASES_TAC >> simp[bind_def, ignore_bind_def, return_def,
       update_accounts_def, add_to_delete_def, finish_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem handle_exception_depth_queue_selector[local]:
  0 < d /\ d <= LENGTH s.contexts /\ e <> SOME Reverted /\
  handle_exception e s = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    (if e <> NONE /\ LENGTH t.contexts < LENGTH s.contexts
     then HD (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
     else HD (MAP (\rb. rb.toDelete) (active_rollbacks d s))) ::
    (if LENGTH t.contexts < LENGTH s.contexts
     then TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
     else TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[] >>
  PairCases_on `h` >> Cases_on `t'` >> gvs[]
  >- (imp_res_tac handle_exception_deletion_projections >> gvs[] >>
      `MAP (\rb. rb.toDelete) (active_rollbacks d t) =
       MAP (\rb. rb.toDelete) (active_rollbacks d s)` by
        (irule active_deletion_queues_exact >> simp[]) >>
      gvs[active_rollbacks_def]) >>
  `d <= LENGTH s.contexts` by simp[] >>
  drule_all handle_exception_queue_selector >> disch_then assume_tac >>
  drule_all handle_exception_deletion_selector >> strip_tac >>
  qpat_assum `MAP _ t.contexts = _`
    (mp_tac o AP_TERM ``LENGTH : address list list -> num``) >>
  simp[] >> strip_tac >>
  Cases_on `e = NONE` >>
  Cases_on `h0.gasUsed <= h0.msgParams.gasLimit` >>
  gvs[active_rollbacks_def]
QED

Theorem handle_step_empty_return_queue_selector[local]:
  0 < d /\ d <= LENGTH s.contexts /\ e <> SOME Reverted /\
  (e = NONE ==> (FST (HD s.contexts)).returnData = [] /\
    (FST (HD s.contexts)).gasUsed <=
      (FST (HD s.contexts)).msgParams.gasLimit) /\
  handle_step e s = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    (if e <> NONE /\ LENGTH t.contexts < LENGTH s.contexts
     then HD (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
     else HD (MAP (\rb. rb.toDelete) (active_rollbacks d s))) ::
    (if LENGTH t.contexts < LENGTH s.contexts
     then TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
     else TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
Proof
  strip_tac >> `s.contexts <> []` by (strip_tac >> gvs[]) >>
  Cases_on `vfm_abort e`
  >- gvs[handle_step_def, reraise_def, active_rollbacks_def] >>
  `?ce cs. handle_create e s = (INR ce : unit + vfmExecution$exception option,cs)` by
    metis_tac[handle_create_INR] >>
  `ce = e` by
    (Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
     drule_all handle_create_control >> strip_tac >>
     Cases_on `e` >> Cases_on `h0.msgParams.outputTo` >>
     gvs[]) >>
  `LENGTH cs.contexts = LENGTH s.contexts` by
    metis_tac[handle_create_preserves_length, SND] >>
  `MAP (\rb. rb.toDelete) (active_rollbacks d cs) =
   MAP (\rb. rb.toDelete) (active_rollbacks d s)` by
    (irule active_deletion_queues_exact >>
     drule_all (SRULE [vfmPreservesTheory.preserves_when_def]
       handle_create_deletion_exact) >> simp[]) >>
  `handle_exception e cs = (r,t)` by
    (qpat_x_assum `handle_step e s = _` mp_tac >>
     gvs[handle_step_def, handle_def]) >>
  `d <= LENGTH cs.contexts` by simp[] >>
  drule_all handle_exception_depth_queue_selector >> simp[]
QED

Theorem step_self_destruct_complete_queue_selector[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  s.contexts = (c,rb)::rest /\
  FLOOKUP c.msgParams.parsed c.pc = SOME SelfDestruct /\
  step s = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    (if 1 <= LENGTH c.stack /\
        (case s.msdomain of Collect dom => T
         | Enforce dom => fIN (w2w (HD c.stack)) dom.addresses) /\
        c.gasUsed +
          (static_gas SelfDestruct +
           zero_warm (if fIN (w2w (HD c.stack)) s.rollback.accesses.addresses
                      then warm_access_cost else cold_access_cost) +
           (if 0 < (lookup_account c.msgParams.callee s.rollback.accounts).balance /\
               account_empty (lookup_account (w2w (HD c.stack)) s.rollback.accounts)
            then self_destruct_new_account_cost else 0)) <= c.msgParams.gasLimit /\
        ~c.msgParams.static
     then (if account_empty (lookup_account c.msgParams.callee s.originalAccounts)
           then c.msgParams.callee :: HD (MAP (\rb. rb.toDelete) (active_rollbacks d s))
           else HD (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
     else if LENGTH t.contexts < LENGTH s.contexts
     then HD (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
     else HD (MAP (\rb. rb.toDelete) (active_rollbacks d s))) ::
    (if LENGTH t.contexts < LENGTH s.contexts
     then TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
     else TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
Proof
  strip_tac >> `s.contexts <> []` by simp[] >>
  Cases_on `(step_self_destruct s : (unit + vfmExecution$exception option) # execution_state)` >>
  rename1 `(step_self_destruct s : (unit + vfmExecution$exception option) # execution_state) = (z,ss)` >>
  `?e. z = INR e` by
    (qpat_x_assum `step_self_destruct s = _` mp_tac >>
     simp[step_self_destruct_def, bind_def, ignore_bind_def,
          finish_def, fail_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  gvs[] >>
  `handle_step e ss = (r,t)` by
    (qpat_x_assum `step s = _` mp_tac >>
     simp[step_def, get_current_context_def, return_def, bind_def,
          step_inst_def, ignore_bind_def, handle_def]) >>
  `s.contexts <> []` by simp[] >>
  drule_all step_self_destruct_handler_control >> strip_tac >>
  drule_all step_self_destruct_deletion_provenance >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  `LENGTH ss.contexts = LENGTH s.contexts` by metis_tac[LENGTH_MAP] >>
  `d <= LENGTH ss.contexts` by simp[] >>
  drule_all handle_step_empty_return_queue_selector >> disch_then assume_tac >>
  drule_all step_self_destruct_queue_selector >>
  disch_then (qspec_then `d` assume_tac) >>
  drule (INST_TYPE [alpha |-> ``:unit``] step_self_destruct_finishes) >>
  strip_tac >>
  Cases_on `e = NONE` >> gvs[active_rollbacks_def]
QED

Theorem step_return_context_control[local]:
  s.contexts <> [] /\ MAP FST s.contexts = MAP FST u.contexts /\
  step_return b s = ((r : unit + vfmExecution$exception option),t) /\
  step_return b u = ((q : unit + vfmExecution$exception option),v) ==>
  r = q /\ MAP FST t.contexts = MAP FST v.contexts
Proof
  Cases_on `s.contexts` >> Cases_on `u.contexts` >> simp[] >>
  PairCases_on `h` >> PairCases_on `h'` >> strip_tac >> gvs[] >>
  qpat_x_assum `step_return b s = _` mp_tac >>
  qpat_x_assum `step_return b u = _` mp_tac >>
  simp[step_return_def, pop_stack_def, memory_expansion_info_def,
       consume_gas_def, expand_memory_def, read_memory_def,
       set_return_data_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def,
       vfmExecutionTheory.finish_def, vfmExecutionTheory.revert_def] >>
  rpt (COND_CASES_TAC >> simp[vfmExecutionTheory.finish_def,
                              vfmExecutionTheory.revert_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem step_return_INR[local]:
  ?e. step_return b s = (INR e : unit + vfmExecution$exception option,
                        SND (step_return b s))
Proof
  Cases_on `s.contexts` >> simp[step_return_def, pop_stack_def,
       memory_expansion_info_def, consume_gas_def, expand_memory_def,
       read_memory_def, set_return_data_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[vfmExecutionTheory.finish_def,
                              vfmExecutionTheory.revert_def])
QED

Theorem step_return_queue_suffix[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  erase_toDelete s = erase_toDelete u /\
  FLOOKUP (FST (HD s.contexts)).msgParams.parsed
    (FST (HD s.contexts)).pc = SOME op /\
  (op = Return \/ op = Revert) /\
  MAP (\rb. rb.toDelete) (active_rollbacks d s) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d u)) /\
  step s = (r,t) /\ step u = (q,v) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d v))
Proof
  strip_tac >>
  `MAP FST s.contexts = MAP FST u.contexts` by
    (qpat_x_assum `erase_toDelete s = _` mp_tac >>
     simp[erase_toDelete_def, execution_state_component_equality] >>
     strip_tac >>
     qpat_x_assum `MAP _ s.contexts = _`
       (mp_tac o Q.AP_TERM `MAP FST`) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.ELIM_UNCURRY, ETA_THM]) >>
  `s.contexts <> [] /\ u.contexts <> []` by
    (Cases_on `s.contexts` >> Cases_on `u.contexts` >> gvs[]) >>
  `FST (HD s.contexts) = FST (HD u.contexts)` by
    (Cases_on `s.contexts` >> Cases_on `u.contexts` >> gvs[]) >>
  `?e ss. step_return (op = Return) s = (INR e : unit + vfmExecution$exception option,ss)` by
    metis_tac[step_return_INR] >>
  `?f us. step_return (op = Return) u = (INR f : unit + vfmExecution$exception option,us)` by
    metis_tac[step_return_INR] >>
  drule_all step_return_context_control >> strip_tac >> gvs[] >>
  `handle_step e ss = (r,t) /\ handle_step e us = (q,v)` by
    (qpat_x_assum `step s = _` mp_tac >>
     qpat_x_assum `step u = _` mp_tac >>
     gvs[step_def, get_current_context_def, return_def, bind_def,
         step_inst_def, ignore_bind_def, handle_def]) >>
  mp_tac (Q.INST [`op` |-> `Return`] step_inst_deletion_exact) >>
  mp_tac (Q.INST [`op` |-> `Revert`] step_inst_deletion_exact) >>
  simp[step_inst_def, vfmPreservesTheory.preserves_when_def] >>
  rpt strip_tac >>
  first_assum (qspec_then `s` (drule_all_then strip_assume_tac)) >>
  first_assum (qspec_then `u` (drule_all_then strip_assume_tac)) >>
  `LENGTH ss.contexts = LENGTH s.contexts` by metis_tac[LENGTH_MAP] >>
  `MAP (\rb. rb.toDelete) (active_rollbacks d ss) =
   MAP (\rb. rb.toDelete) (active_rollbacks d s)` by
    (irule active_deletion_queues_exact >> simp[]) >>
  `MAP (\rb. rb.toDelete) (active_rollbacks d us) =
   MAP (\rb. rb.toDelete) (active_rollbacks d u)` by
    (irule active_deletion_queues_exact >> simp[]) >>
  `d <= LENGTH ss.contexts /\ ss.contexts <> []` by
    (Cases_on `ss.contexts` >> gvs[]) >>
  `MAP (\rb. rb.toDelete) (active_rollbacks d ss) =
   MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d us))` by simp[] >>
  drule_all handle_step_queue_suffix >> simp[]
QED

Theorem inc_pc_or_jump_exception_class[local]:
  inc_pc_or_jump op s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted
Proof
  simp[inc_pc_or_jump_def] >> IF_CASES_TAC
  >- simp[return_def] >>
  Cases_on `s.contexts` >>
  simp[get_current_context_def, bind_def, return_def, fail_def,
       assert_def, set_current_context_def] >>
  Cases_on `(FST h).jumpDest` >>
  simp[set_current_context_def, ignore_bind_def, bind_def,
       assert_def, return_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[])
QED

Theorem step_binop_exception_class[local]:
  step_binop op f s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted
Proof
  simp[step_binop_def, pop_stack_def, consume_gas_def, push_stack_def,
       get_current_context_def, set_current_context_def, ignore_bind_def,
       bind_def, return_def, assert_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[])
QED

Theorem bind_exception_class[local]:
  (!s e t. f s = (INR e,t) ==> P e) /\
  (!x s e t. g x s = (INR e,t) ==> P e) ==>
  (vfmExecution$bind f g s = (INR e,t) ==> P e)
Proof
  rpt strip_tac >> gvs[bind_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem basic_exception_class[local]:
  (get_current_context s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (set_current_context c s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (pop_stack n s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (push_stack v s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (consume_gas n s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted)
Proof
  simp[pop_stack_def, push_stack_def, consume_gas_def,
       get_current_context_def, set_current_context_def, ignore_bind_def,
       bind_def, return_def, assert_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[])
QED

Theorem step_monop_exception_class[local]:
  step_monop op f s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted
Proof
  rewrite_tac[step_monop_def, ignore_bind_def] >>
  ho_match_mp_tac bind_exception_class >> conj_tac
  >- metis_tac[basic_exception_class] >>
  rpt gen_tac >> ho_match_mp_tac bind_exception_class >>
  conj_tac >> metis_tac[basic_exception_class]
QED

Theorem context_exception_class[local]:
  (get_callee s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (get_call_data s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (get_current_code s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (get_code a s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (get_gas_left s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (get_original s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (get_return_data_check off len s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (set_jump_dest j s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (push_logs logs s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (update_gas_refund refunds s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (assert_not_static s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted)
Proof
  PairCases_on `refunds` >>
  simp[get_callee_def, get_call_data_def, get_current_code_def, get_code_def,
       get_gas_left_def, get_original_def, get_return_data_check_def,
       get_return_data_def, set_jump_dest_def, push_logs_def,
       update_gas_refund_def, assert_not_static_def, get_static_def,
       get_current_context_def, set_current_context_def, get_accounts_def,
       ignore_bind_def, bind_def, return_def, assert_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[])
QED

Theorem access_exception_class[local]:
  (access_address a s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (access_slot key s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted)
Proof
  Cases_on `s.msdomain` >>
  simp[access_address_def, access_slot_def, domain_check_def, set_domain_def,
       ignore_bind_def, bind_def, return_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[]) >> rpt strip_tac >> gvs[]
QED

Theorem memory_exception_class[local]:
  (memory_expansion_info off len s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (expand_memory n s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (read_memory off len s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (write_memory off bytes s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted)
Proof
  simp[memory_expansion_info_def, expand_memory_def, read_memory_def,
       write_memory_def, get_current_context_def, set_current_context_def,
       ignore_bind_def, bind_def, return_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[])
QED

Theorem stack_instruction_exception_class[local]:
  (step_modop op f s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_context op g s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_txParams op h s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_exp s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_push n ws s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_pop s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_dup n s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_swap n s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted)
Proof
  rewrite_tac[step_modop_def, step_context_def, step_txParams_def,
              step_exp_def, step_push_def, step_pop_def, step_dup_def,
              step_swap_def, ignore_bind_def, LET_THM] >>
  rpt conj_tac >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[get_tx_params_def, return_def, assert_def] >>
  rpt (COND_CASES_TAC >> simp[])
  >>~- ([`pop_stack _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`consume_gas _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`push_stack _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`get_current_context _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`set_current_context _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >> rewrite_tac[ignore_bind_def]
  >> rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac])
  >> simp[assert_def]
  >> rpt (COND_CASES_TAC >> simp[])
  >> metis_tac[basic_exception_class]
QED

Theorem memory_instruction_exception_class[local]:
  (step_keccak256 s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_mload s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_mstore op s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_jump s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_jumpi s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_log n s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted)
Proof
  pure_rewrite_tac [step_keccak256_def, step_mload_def, step_mstore_def,
             step_jump_def, step_jumpi_def, step_log_def, ignore_bind_def,
             LET_THM] >>
  rpt conj_tac >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[LET_THM, combinTheory.o_DEF] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  metis_tac[basic_exception_class, memory_exception_class, context_exception_class]
QED

Theorem account_instruction_exception_class[local]:
  (step_balance s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_ext_code_size s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_ext_code_hash s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_self_balance s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_block_hash s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_blob_hash s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_call_data_load s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_sload transient s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted)
Proof
  Cases_on `transient` >>
  rewrite_tac[step_balance_def, step_ext_code_size_def, step_ext_code_hash_def,
              step_self_balance_def, step_block_hash_def, step_blob_hash_def,
              step_call_data_load_def, step_sload_def, ignore_bind_def, LET_THM] >>
  rpt conj_tac >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[get_accounts_def, get_tx_params_def, get_tStorage_def, return_def] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[get_accounts_def, get_tx_params_def, get_tStorage_def, return_def] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  metis_tac[basic_exception_class, context_exception_class, access_exception_class]
QED

Theorem copy_to_memory_exception_class[local]:
  copy_to_memory gas off src len getSource s = (INR e,t) ==>
  (!f u ex v. getSource = SOME f /\ f u = (INR ex,v) ==>
     ex <> NONE /\ ex <> SOME Reverted) ==>
  e <> NONE /\ e <> SOME Reverted
Proof
  reverse (rpt disch_tac) >>
  qpat_x_assum `copy_to_memory _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `max_expansion_range (off,len) (src,len)` >>
  Cases_on `getSource` >>
  simp[copy_to_memory_def, ignore_bind_def, LET_THM] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[return_def] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  metis_tac[basic_exception_class, memory_exception_class]
QED

Theorem copy_instruction_exception_class[local]:
  (!f s e t. getSource = SOME f /\ f s = (INR e,t) ==>
     e <> NONE /\ e <> SOME Reverted) ==>
  step_copy_to_memory op getSource s = (INR e,t) ==>
  e <> NONE /\ e <> SOME Reverted
Proof
  strip_tac >> rewrite_tac[step_copy_to_memory_def, LET_THM] >>
  ho_match_mp_tac bind_exception_class >> conj_tac
  >- metis_tac[basic_exception_class] >>
  rpt gen_tac >> metis_tac[copy_to_memory_exception_class]
QED

Theorem special_copy_exception_class[local]:
  (step_return_data_copy s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (step_ext_code_copy s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted)
Proof
  rewrite_tac[step_return_data_copy_def, step_ext_code_copy_def,
              ignore_bind_def, LET_THM] >>
  conj_tac >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac])
  >>~- ([`pop_stack _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`access_address _ _ = _ ==> _`], metis_tac[access_exception_class]) >>
  simp[] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac])
  >>~- ([`access_address _ _ = _ ==> _`], metis_tac[access_exception_class]) >>
  strip_tac >> drule copy_to_memory_exception_class >>
  disch_then irule >> simp[] >> metis_tac[context_exception_class]
QED

Theorem storage_instruction_exception_class[local]:
  (!a k v s e t. step_sstore_gas_consumption a k v s = (INR e,t) ==>
    e <> NONE /\ e <> SOME Reverted) /\
  (step_sstore transient s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted)
Proof
  conj_asm1_tac
  >- (rewrite_tac[step_sstore_gas_consumption_def, ignore_bind_def, LET_THM] >>
      rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
      simp[get_accounts_def, return_def, assert_def] >>
      rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
      metis_tac[basic_exception_class, context_exception_class, access_exception_class]) >>
  Cases_on `transient` >>
  rewrite_tac[step_sstore_def, ignore_bind_def, LET_THM] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[write_transient_storage_def, write_storage_def, return_def]
  >>~- ([`pop_stack _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`get_callee _ = _ ==> _`], metis_tac[context_exception_class]) >>
  rewrite_tac[ignore_bind_def] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[get_tStorage_def, set_tStorage_def, get_accounts_def, update_accounts_def, return_def] >>
  metis_tac[basic_exception_class, context_exception_class]
QED

Theorem step_inst_exception_class[local]:
  op <> Stop /\ op <> Return /\ op <> Revert /\ op <> SelfDestruct /\
  ~is_call op /\ step_inst op s = (INR e,t) ==>
  e <> NONE /\ e <> SOME Reverted
Proof
  Cases_on `op` >>
  simp[is_call_def, step_inst_def, step_msgParams_def, fail_def] >>
  disch_tac
  >>~- ([`step_binop _ _ _ = _`], metis_tac[step_binop_exception_class])
  >>~- ([`step_monop _ _ _ = _`], metis_tac[step_monop_exception_class])
  >>~- ([`step_modop _ _ _ = _`], metis_tac[stack_instruction_exception_class])
  >>~- ([`step_context _ _ _ = _`], metis_tac[stack_instruction_exception_class])
  >>~- ([`step_txParams _ _ _ = _`], metis_tac[stack_instruction_exception_class])
  >>~- ([`step_exp _ = _`], metis_tac[stack_instruction_exception_class])
  >>~- ([`step_pop _ = _`], metis_tac[stack_instruction_exception_class])
  >>~- ([`step_push _ _ _ = _`], metis_tac[stack_instruction_exception_class])
  >>~- ([`step_dup _ _ = _`], metis_tac[stack_instruction_exception_class])
  >>~- ([`step_swap _ _ = _`], metis_tac[stack_instruction_exception_class])
  >>~- ([`step_keccak256 _ = _`], metis_tac[memory_instruction_exception_class])
  >>~- ([`step_mload _ = _`], metis_tac[memory_instruction_exception_class])
  >>~- ([`step_mstore _ _ = _`], metis_tac[memory_instruction_exception_class])
  >>~- ([`step_jump _ = _`], metis_tac[memory_instruction_exception_class])
  >>~- ([`step_jumpi _ = _`], metis_tac[memory_instruction_exception_class])
  >>~- ([`step_log _ _ = _`], metis_tac[memory_instruction_exception_class])
  >>~- ([`step_balance _ = _`], metis_tac[account_instruction_exception_class])
  >>~- ([`step_ext_code_size _ = _`], metis_tac[account_instruction_exception_class])
  >>~- ([`step_ext_code_hash _ = _`], metis_tac[account_instruction_exception_class])
  >>~- ([`step_self_balance _ = _`], metis_tac[account_instruction_exception_class])
  >>~- ([`step_block_hash _ = _`], metis_tac[account_instruction_exception_class])
  >>~- ([`step_blob_hash _ = _`], metis_tac[account_instruction_exception_class])
  >>~- ([`step_call_data_load _ = _`], metis_tac[account_instruction_exception_class])
  >>~- ([`step_sload _ _ = _`], metis_tac[account_instruction_exception_class])
  >>~- ([`step_sstore _ _ = _`], metis_tac[storage_instruction_exception_class])
  >>~- ([`step_ext_code_copy _ = _`], metis_tac[special_copy_exception_class])
  >>~- ([`step_return_data_copy _ = _`], metis_tac[special_copy_exception_class])
  >>~- ([`consume_gas _ _ = _`], metis_tac[basic_exception_class]) >>
  drule_at (Pos last) copy_instruction_exception_class >>
  (impl_tac >- (simp[] >> metis_tac[context_exception_class])) >> simp[]
QED

Theorem handle_step_error_queue_selector[local]:
  0 < d /\ d <= LENGTH s.contexts /\ e <> NONE /\ e <> SOME Reverted /\
  handle_step e s = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    if LENGTH t.contexts < LENGTH s.contexts then
      HD (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s))) ::
      TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
    else MAP (\rb. rb.toDelete) (active_rollbacks d s)
Proof
  strip_tac >>
  drule_at (Pos last) handle_step_empty_return_queue_selector >>
  disch_then (qspec_then `d` mp_tac) >>
  Cases_on `LENGTH t.contexts < LENGTH s.contexts` >>
  simp[active_rollbacks_def]
QED

Theorem proceed_call_exception_not_reverted[local]:
  proceed_call op sender address value ao az code gas rd s = (INR e,t) ==>
  e <> SOME Reverted
Proof
  Cases_on `s.contexts` >>
  simp[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_caller_def, get_value_def,
       get_static_def, get_current_context_def, push_context_def,
       vfmExecutionTheory.update_accounts_def, return_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[]) >>
  simp[vfmExecutionTheory.update_accounts_def, return_def] >>
  strip_tac >>
  drule_at (Pos last) vfmRunWithinFrameTheory.dispatch_precompiles_inr_not_reverted_not_abort >>
  simp[]
QED

Theorem call_create_helpers_exception_class[local]:
  (abort_unuse n s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (abort_call_value n s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (abort_create_exists a s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted) /\
  (proceed_create a b v code gas s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted)
Proof
  rewrite_tac[abort_unuse_def, abort_call_value_def, abort_create_exists_def,
              proceed_create_def, ignore_bind_def, LET_THM] >>
  rpt conj_tac >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[unuse_gas_def, inc_pc_def, set_return_data_def,
       vfmExecutionTheory.update_accounts_def, get_rollback_def,
       get_original_def, set_original_def, push_context_def,
       get_current_context_def, set_current_context_def,
       return_def, fail_def] >>
  rewrite_tac[ignore_bind_def] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[assert_def, return_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[])
  >>~- ([`get_current_context _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`set_current_context _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`push_stack _ _ = _ ==> _`], metis_tac[basic_exception_class]) >>
  simp[vfmExecutionTheory.get_rollback_def, get_original_def,
       set_original_def, push_context_def, vfmExecutionTheory.update_accounts_def,
       return_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[])
QED

Theorem step_create_exception_class[local]:
  step_create two s = (INR e,t) ==> e <> NONE /\ e <> SOME Reverted
Proof
  rewrite_tac[step_create_def, ignore_bind_def, LET_THM] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[get_accounts_def, return_def, assert_def] >>
  rpt (COND_CASES_TAC >> simp[])
  >>~- ([`pop_stack _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`consume_gas _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`memory_expansion_info _ _ _ = _ ==> _`], metis_tac[memory_exception_class])
  >>~- ([`expand_memory _ _ = _ ==> _`], metis_tac[memory_exception_class])
  >>~- ([`read_memory _ _ _ = _ ==> _`], metis_tac[memory_exception_class])
  >>~- ([`get_callee _ = _ ==> _`], metis_tac[context_exception_class])
  >>~- ([`get_gas_left _ = _ ==> _`], metis_tac[context_exception_class]) >>
  rewrite_tac[ignore_bind_def] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[assert_def, get_num_contexts_def, return_def] >>
  rpt (COND_CASES_TAC >> simp[])
  >>~- ([`memory_expansion_info _ _ _ = _ ==> _`], metis_tac[memory_exception_class])
  >>~- ([`expand_memory _ _ = _ ==> _`], metis_tac[memory_exception_class])
  >>~- ([`read_memory _ _ _ = _ ==> _`], metis_tac[memory_exception_class])
  >>~- ([`consume_gas _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`get_callee _ = _ ==> _`], metis_tac[context_exception_class])
  >>~- ([`get_gas_left _ = _ ==> _`], metis_tac[context_exception_class])
  >>~- ([`abort_unuse _ _ = _ ==> _`], metis_tac[call_create_helpers_exception_class])
  >>~- ([`abort_create_exists _ _ = _ ==> _`], metis_tac[call_create_helpers_exception_class])
  >>~- ([`proceed_create _ _ _ _ _ _ = _ ==> _`], metis_tac[call_create_helpers_exception_class])
  >>~- ([`access_address _ _ = _ ==> _`], metis_tac[access_exception_class]) >>
  simp[vfmExecutionTheory.get_accounts_def, assert_not_static_def,
       set_return_data_def, ensure_storage_in_domain_def, ignore_bind_def] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[assert_def, return_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[]) >>
  simp[get_static_def, vfmExecutionTheory.get_accounts_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[]) >>
  all_tac
  >>~- ([`access_address _ _ = _ ==> _`], metis_tac[access_exception_class])
  >>~- ([`abort_create_exists _ _ = _ ==> _`], metis_tac[call_create_helpers_exception_class])
  >>~- ([`proceed_create _ _ _ _ _ _ = _ ==> _`], metis_tac[call_create_helpers_exception_class]) >>
  Cases_on `s.msdomain` >>
  simp[domain_check_def, return_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[]) >> rpt strip_tac >>
  gvs[set_domain_def, ignore_bind_def, bind_def, return_def]
QED

Theorem step_call_exception_not_reverted[local]:
  step_call op s = (INR e,t) ==> e <> SOME Reverted
Proof
  rewrite_tac[step_call_def, ignore_bind_def, LET_THM] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[vfmExecutionTheory.get_accounts_def, return_def, assert_def] >>
  rpt (COND_CASES_TAC >> simp[])
  >>~- ([`pop_stack _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`memory_expansion_info _ _ _ = _ ==> _`], metis_tac[memory_exception_class])
  >>~- ([`access_address _ _ = _ ==> _`], metis_tac[access_exception_class])
  >>~- ([`get_gas_left _ = _ ==> _`], metis_tac[context_exception_class]) >>
  simp[AllCaseEqs(), ignore_bind_def] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[return_def, assert_def] >>
  rpt (COND_CASES_TAC >> simp[])
  >>~- ([`pop_stack _ _ = _ ==> _`], metis_tac[basic_exception_class]) >>
  pairarg_tac >> simp[] >>
  rpt (FIRST [gen_tac, ho_match_mp_tac bind_exception_class >> conj_tac]) >>
  simp[vfmExecutionTheory.get_accounts_def, return_def]
  >>~- ([`memory_expansion_info _ _ _ = _ ==> _`], metis_tac[memory_exception_class])
  >>~- ([`access_address _ _ = _ ==> _`], metis_tac[access_exception_class]) >>
  rpt (FIRST [gen_tac,
    ho_match_mp_tac bind_exception_class >> conj_tac,
    pairarg_tac >> simp[], CASE_TAC >> simp[return_def]]) >>
  simp[return_def, get_num_contexts_def] >>
  rpt (COND_CASES_TAC >> simp[])
  >>~- ([`access_address _ _ = _ ==> _`], metis_tac[access_exception_class])
  >>~- ([`get_gas_left _ = _ ==> _`], metis_tac[context_exception_class])
  >>~- ([`get_callee _ = _ ==> _`], metis_tac[context_exception_class])
  >>~- ([`consume_gas _ _ = _ ==> _`], metis_tac[basic_exception_class])
  >>~- ([`expand_memory _ _ = _ ==> _`], metis_tac[memory_exception_class])
  >>~- ([`abort_call_value _ _ = _ ==> _`], metis_tac[call_create_helpers_exception_class])
  >>~- ([`abort_unuse _ _ = _ ==> _`], metis_tac[call_create_helpers_exception_class])
  >>~- ([`proceed_call _ _ _ _ _ _ _ _ _ _ = _ ==> _`], metis_tac[proceed_call_exception_not_reverted]) >>
  simp[assert_not_static_def, set_return_data_def, get_static_def,
       ignore_bind_def, bind_def, get_current_context_def,
       set_current_context_def, assert_def, return_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[]) >> rpt strip_tac >> gvs[]
QED

Theorem bind_normal_finish_growth[local]:
  cp g /\ (!s t. g s = (INR NONE,t) ==> F) /\
  (!x s t. s.contexts <> [] /\ f x s = (INR NONE,t) ==>
     LENGTH s.contexts < LENGTH t.contexts) ==>
  !s t. s.contexts <> [] /\ bind g f s = (INR NONE,t) ==>
    LENGTH s.contexts < LENGTH t.contexts
Proof
  rw[bind_def, AllCaseEqs()] >>
  metis_tac[vfmSameFrameTheory.cp_imp_length_contexts_preserved,
            vfmStaticCallsTheory.cp_contexts_ne_pair]
QED

Theorem step_call_normal_finish_growth[local]:
  !s t. s.contexts <> [] /\ step_call op s = (INR NONE,t) ==>
    LENGTH s.contexts < LENGTH t.contexts
Proof
  rewrite_tac[step_call_def, ignore_bind_def, LET_THM] >>
  simp[LET_THM] >>
  ho_match_mp_tac bind_normal_finish_growth >>
  simp[] >> conj_tac
  >- metis_tac[basic_exception_class] >>
  gen_tac >> pairarg_tac >> simp[] >>
  rpt (FIRST [
    ho_match_mp_tac bind_normal_finish_growth >> simp[] >> conj_tac,
    gen_tac]) >>
  all_tac
  >>~- ([`memory_expansion_info _ _ _ <> _`], metis_tac[memory_exception_class])
  >>~- ([`access_address _ _ <> _`], metis_tac[access_exception_class]) >>
  simp[vfmExecutionTheory.get_accounts_def, return_def] >>
  all_tac
  >- (CASE_TAC >> simp[bind_def, return_def, AllCaseEqs()] >>
      metis_tac[access_exception_class]) >>
  pairarg_tac >> simp[] >>
  rpt (FIRST [ho_match_mp_tac bind_normal_finish_growth >> simp[] >> conj_tac,
              gen_tac]) >>
  map_every qid_spec_tac [`t`,`s`] >>
  ho_match_mp_tac bind_normal_finish_growth >> simp[] >>
  conj_tac >- metis_tac[context_exception_class] >>
  gen_tac >> pairarg_tac >> simp[] >>
  rpt (FIRST [ho_match_mp_tac bind_normal_finish_growth >> simp[] >> conj_tac,
              gen_tac]) >>
  all_tac
  >>~- ([`consume_gas _ _ <> _`], metis_tac[basic_exception_class])
  >>~- ([`expand_memory _ _ <> _`], metis_tac[memory_exception_class])
  >>~- ([`get_callee _ <> _`], metis_tac[context_exception_class]) >>
  all_tac
  >- (COND_CASES_TAC >> simp[return_def, assert_not_static_def,
        get_static_def, get_current_context_def, bind_def,
        assert_def, fail_def] >> rpt (COND_CASES_TAC >> simp[])) >>
  rpt (COND_CASES_TAC >> simp[]) >>
  all_tac
  >>~- ([`_ /\ abort_call_value _ _ = _ ==> _`],
        metis_tac[call_create_helpers_exception_class]) >>
  simp[set_return_data_def, get_num_contexts_def, bind_def, return_def,
       get_current_context_def, set_current_context_def, fail_def] >>
  rpt (COND_CASES_TAC >> simp[]) >>
  rpt strip_tac >>
  all_tac
  >>~- ([`abort_unuse _ _ = _`], metis_tac[call_create_helpers_exception_class]) >>
  drule_at (Pos last) vfmAccountDeletionTheory.proceed_call_deletion_projections >>
  simp[] >> Cases_on `s.contexts` >> gvs[]
QED

Theorem handle_step_saved_current_queue_selector[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  s.contexts = (callee,rb)::parent::rest /\
  s.rollback.toDelete = rb.toDelete /\
  handle_step e s = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    if LENGTH t.contexts = LENGTH s.contexts then
      MAP (\rb. rb.toDelete) (active_rollbacks d s)
    else
      HD (MAP (\rb. rb.toDelete) (active_rollbacks d s)) ::
      TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
Proof
  strip_tac >>
  `s.contexts <> []` by metis_tac[NOT_CONS_NIL] >>
  `t.rollback.toDelete = s.rollback.toDelete` by
    (drule_all handle_step_deletion_projections >>
     strip_tac >> fs[HD, SND]) >>
  drule_all handle_step_deletion_projections >>
  disch_then (strip_assume_tac o CONJUNCT2 o CONJUNCT2 o CONJUNCT2)
  >- (simp[] >> irule active_deletion_queues_exact >> simp[]) >>
  `LENGTH t.contexts <> LENGTH s.contexts` by decide_tac >>
  simp[active_deletion_queues_head] >>
  metis_tac[active_deletion_queues_saved_pop]
QED

Theorem step_ordinary_body_queue_selector[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  op <> Stop /\ op <> Return /\ op <> Revert /\ op <> SelfDestruct /\
  ~is_call op /\
  handle (ignore_bind (step_inst op) (inc_pc_or_jump op)) handle_step s = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    if LENGTH t.contexts < LENGTH s.contexts then
      HD (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s))) ::
      TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
    else MAP (\rb. rb.toDelete) (active_rollbacks d s)
Proof
  strip_tac >>
  `s.contexts <> []` by (Cases_on `s.contexts` >> gvs[]) >>
  `op <> Create /\ op <> Create2 /\ op <> Call /\ op <> CallCode /\
   op <> DelegateCall /\ op <> StaticCall` by
    (Cases_on `op` >> gvs[is_call_def]) >>
  `!q u. step_inst op s = (q,u) ==>
    u.contexts <> [] /\ LENGTH u.contexts = LENGTH s.contexts /\
    MAP (\rb. rb.toDelete) (active_rollbacks d u) =
    MAP (\rb. rb.toDelete) (active_rollbacks d s)` by
    (rpt gen_tac >> disch_tac >>
     drule_all step_inst_deletion_exact >>
     disch_then (assume_tac o REWRITE_RULE
       [vfmPreservesTheory.preserves_when_def]) >>
     `u.contexts <> [] /\
      MAP (\p. (SND p).toDelete) u.contexts =
        MAP (\p. (SND p).toDelete) s.contexts /\
      u.rollback.toDelete = s.rollback.toDelete` by metis_tac[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- metis_tac[LENGTH_MAP] >>
     irule active_deletion_queues_exact >> simp[]) >>
  qpat_x_assum `handle _ _ s = _` mp_tac >>
  pure_rewrite_tac[handle_def] >>
  Cases_on `step_inst op s : (unit + vfmExecution$exception option) # execution_state` >>
  rename1 `step_inst op s = (q,u)` >>
  qpat_x_assum `!q' u'. _` (qspecl_then [`q`,`u`] mp_tac) >>
  simp_tac bool_ss [PAIR_EQ, REFL_CLAUSE] >> strip_tac >>
  reverse (Cases_on `q`) >> simp[ignore_bind_def, bind_def]
  >- (strip_tac >>
      drule_all step_inst_exception_class >> strip_tac >>
      drule_at (Pos last) handle_step_error_queue_selector >>
      disch_then (qspec_then `d` mp_tac) >> simp[]) >>
  Cases_on `inc_pc_or_jump op u : (unit + vfmExecution$exception option) # execution_state` >>
  rename1 `inc_pc_or_jump op u = (q,v)` >>
  `v.contexts <> [] /\
   MAP (\p. (SND p).toDelete) v.contexts =
     MAP (\p. (SND p).toDelete) u.contexts /\
   v.rollback.toDelete = u.rollback.toDelete` by
    (mp_tac inc_pc_or_jump_deletion_exact >>
     pure_rewrite_tac[vfmPreservesTheory.preserves_when_def] >>
     disch_then (qspecl_then [`u`,`q`,`v`] mp_tac) >> simp[]) >>
  `LENGTH v.contexts = LENGTH u.contexts` by metis_tac[LENGTH_MAP] >>
  `MAP (\rb. rb.toDelete) (active_rollbacks d v) =
   MAP (\rb. rb.toDelete) (active_rollbacks d u)` by
    (irule active_deletion_queues_exact >> simp[]) >>
  Cases_on `q` >> simp[] >> strip_tac
  >- (gvs[] >> simp[]) >>
  drule inc_pc_or_jump_exception_class >> strip_tac >>
  drule_at (Pos last) handle_step_error_queue_selector >>
  disch_then (qspec_then `d` mp_tac) >> simp[]
QED

Theorem step_ordinary_queue_selector[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  FLOOKUP (FST (HD s.contexts)).msgParams.parsed
    (FST (HD s.contexts)).pc = SOME op /\
  op <> Stop /\ op <> Return /\ op <> Revert /\ op <> SelfDestruct /\
  ~is_call op /\ step s = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    if LENGTH t.contexts < LENGTH s.contexts then
      HD (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s))) ::
      TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
    else MAP (\rb. rb.toDelete) (active_rollbacks d s)
Proof
  strip_tac >>
  `s.contexts <> []` by (Cases_on `s.contexts` >> gvs[]) >>
  irule step_ordinary_body_queue_selector >> simp[] >>
  qexistsl [`op`,`r`] >> simp[] >>
  qpat_x_assum `step s = _` mp_tac >>
  simp[step_def, handle_def, get_current_context_def, bind_def, return_def]
QED

Theorem step_stop_control[local]:
  s.contexts <> [] ==>
  step_inst Stop s =
    (INR NONE : unit + vfmExecution$exception option,
     s with contexts :=
       (FST (HD s.contexts) with returnData := [], SND (HD s.contexts)) ::
       TL s.contexts)
Proof
  Cases_on `s.contexts` >> simp[] >> PairCases_on `h` >>
  simp[step_inst_def, set_return_data_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       vfmExecutionTheory.finish_def]
QED

Theorem step_stop_queue_suffix[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  erase_toDelete s = erase_toDelete u /\
  (FLOOKUP (FST (HD s.contexts)).msgParams.parsed
     (FST (HD s.contexts)).pc = SOME Stop \/
   FLOOKUP (FST (HD s.contexts)).msgParams.parsed
     (FST (HD s.contexts)).pc = NONE /\
   LENGTH (FST (HD s.contexts)).msgParams.code <= (FST (HD s.contexts)).pc) /\
  MAP (\rb. rb.toDelete) (active_rollbacks d s) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d u)) /\
  step s = (r,t) /\ step u = (q,v) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d v))
Proof
  strip_tac >>
  `MAP FST s.contexts = MAP FST u.contexts` by
    (qpat_x_assum `erase_toDelete s = _` mp_tac >>
     simp[erase_toDelete_def, execution_state_component_equality] >>
     strip_tac >>
     qpat_x_assum `MAP _ s.contexts = _`
       (mp_tac o Q.AP_TERM `MAP FST`) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.ELIM_UNCURRY, ETA_THM]) >>
  `s.contexts <> [] /\ u.contexts <> []` by
    (Cases_on `s.contexts` >> Cases_on `u.contexts` >> gvs[]) >>
  `FST (HD s.contexts) = FST (HD u.contexts)` by
    (Cases_on `s.contexts` >> Cases_on `u.contexts` >> gvs[]) >>
  gs[] >>
  qpat_x_assum `step s = _` mp_tac >>
  qpat_x_assum `step u = _` mp_tac >>
  simp[step_def, get_current_context_def, return_def, bind_def,
       ignore_bind_def, handle_def, step_stop_control] >>
  ntac 2 strip_tac >>
  qmatch_asmsub_abbrev_tac `handle_step NONE ss = (r,t)` >>
  qmatch_asmsub_abbrev_tac `handle_step NONE us = (q,v)` >>
  `LENGTH ss.contexts = LENGTH s.contexts /\ ss.contexts <> [] /\
   MAP FST ss.contexts = MAP FST us.contexts` by
    (map_every qunabbrev_tac [`ss`,`us`] >>
     Cases_on `s.contexts` >> Cases_on `u.contexts` >> gvs[]) >>
  `MAP (\rb. rb.toDelete) (active_rollbacks d ss) =
   MAP (\rb. rb.toDelete) (active_rollbacks d s)` by
    (irule active_deletion_queues_exact >>
     simp[Abbr `ss`] >> Cases_on `s.contexts` >> gvs[]) >>
  `MAP (\rb. rb.toDelete) (active_rollbacks d us) =
   MAP (\rb. rb.toDelete) (active_rollbacks d u)` by
    (irule active_deletion_queues_exact >>
     simp[Abbr `us`] >> Cases_on `u.contexts` >> gvs[]) >>
  `d <= LENGTH ss.contexts /\
   MAP (\rb. rb.toDelete) (active_rollbacks d ss) =
   MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d us))` by
    metis_tac[] >>
  drule_all handle_step_queue_suffix >> simp[]
QED

Theorem step_missing_opcode_queue_suffix[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  erase_toDelete s = erase_toDelete u /\
  FLOOKUP (FST (HD s.contexts)).msgParams.parsed
    (FST (HD s.contexts)).pc = NONE /\
  MAP (\rb. rb.toDelete) (active_rollbacks d s) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d u)) /\
  step s = (r,t) /\ step u = (q,v) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d v))
Proof
  strip_tac >>
  Cases_on `LENGTH (FST (HD s.contexts)).msgParams.code <=
            (FST (HD s.contexts)).pc`
  >- (irule step_stop_queue_suffix >> metis_tac[]) >>
  `MAP FST s.contexts = MAP FST u.contexts` by
    (qpat_x_assum `erase_toDelete s = _` mp_tac >>
     simp[erase_toDelete_def, execution_state_component_equality] >>
     strip_tac >>
     qpat_x_assum `MAP _ s.contexts = _`
       (mp_tac o Q.AP_TERM `MAP FST`) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.ELIM_UNCURRY, ETA_THM]) >>
  `s.contexts <> [] /\ u.contexts <> []` by
    (Cases_on `s.contexts` >> Cases_on `u.contexts` >> gvs[]) >>
  `FST (HD s.contexts) = FST (HD u.contexts)` by
    (Cases_on `s.contexts` >> Cases_on `u.contexts` >> gvs[]) >>
  gs[] >>
  `handle_step (SOME InvalidOpcode) s = (r,t) /\
   handle_step (SOME InvalidOpcode) u = (q,v)` by
    (qpat_x_assum `step s = _` mp_tac >>
     qpat_x_assum `step u = _` mp_tac >>
     simp[step_def, get_current_context_def, return_def, bind_def,
          handle_def, step_inst_def, fail_def]) >>
  drule_all handle_step_queue_suffix >> simp[]
QED

Theorem handle_step_same_or_push_queue_selector[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  u.rollback.toDelete = s.rollback.toDelete /\
  (MAP (\p. (SND p).toDelete) u.contexts =
     MAP (\p. (SND p).toDelete) s.contexts \/
   MAP (\p. (SND p).toDelete) u.contexts =
     s.rollback.toDelete :: MAP (\p. (SND p).toDelete) s.contexts) /\
  e <> SOME Reverted /\
  (e = NONE ==> LENGTH s.contexts < LENGTH u.contexts) /\
  handle_step e u = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    if LENGTH t.contexts < LENGTH s.contexts then
      HD (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s))) ::
      TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
    else if LENGTH t.contexts = LENGTH s.contexts then
      MAP (\rb. rb.toDelete) (active_rollbacks d s)
    else HD (MAP (\rb. rb.toDelete) (active_rollbacks d s)) ::
      MAP (\rb. rb.toDelete) (active_rollbacks d s)
Proof
  strip_tac
  >- (`LENGTH u.contexts = LENGTH s.contexts` by metis_tac[LENGTH_MAP] >>
      `e <> NONE /\ u.contexts <> []` by
        (conj_tac >- (strip_tac >> fs[]) >>
         strip_tac >> fs[LENGTH_NIL]) >>
      `MAP (\rb. rb.toDelete) (active_rollbacks d u) =
       MAP (\rb. rb.toDelete) (active_rollbacks d s)` by
        (irule active_deletion_queues_exact >> simp[]) >>
      drule_at (Pos last) handle_step_error_queue_selector >>
      disch_then (qspec_then `d` mp_tac) >> simp[] >>
      drule_all handle_step_deletion_projections >>
      strip_tac >> simp[] >> decide_tac) >>
  `LENGTH u.contexts = SUC (LENGTH s.contexts)` by
    metis_tac[LENGTH_MAP, LENGTH] >>
  `MAP (\rb. rb.toDelete) (active_rollbacks d u) =
   HD (MAP (\rb. rb.toDelete) (active_rollbacks d s)) ::
   MAP (\rb. rb.toDelete) (active_rollbacks d s)` by
    (irule active_deletion_queues_saved_push >> simp[]) >>
  `?callee rb parent rest. u.contexts = (callee,rb)::parent::rest /\
     u.rollback.toDelete = rb.toDelete` by
    (Cases_on `u.contexts` >> gvs[] >> PairCases_on `h` >>
     Cases_on `t'` >> gvs[]) >>
  `MAP (\rb. rb.toDelete) (active_rollbacks d t) =
   if LENGTH t.contexts = LENGTH u.contexts then
     MAP (\rb. rb.toDelete) (active_rollbacks d u)
   else HD (MAP (\rb. rb.toDelete) (active_rollbacks d u)) ::
     TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d u)))` by
    (irule handle_step_saved_current_queue_selector >> simp[] >> metis_tac[]) >>
  `u.contexts <> []` by simp[] >>
  `LENGTH t.contexts = LENGTH u.contexts \/
   LENGTH t.contexts = LENGTH s.contexts` by
    (drule_all handle_step_deletion_projections >> strip_tac >> decide_tac)
  >- (`~(LENGTH t.contexts < LENGTH s.contexts) /\
       LENGTH t.contexts <> LENGTH s.contexts` by decide_tac >>
      asm_rewrite_tac[]) >>
  `~(LENGTH t.contexts < LENGTH s.contexts) /\
   LENGTH t.contexts <> LENGTH u.contexts` by decide_tac >>
  asm_rewrite_tac[HD, TL] >>
  simp[active_rollbacks_def]
QED

Theorem step_call_create_deletion_control[local]:
  s.contexts <> [] /\ is_call op /\ step_inst op s = (q,u) ==>
  u.rollback.toDelete = s.rollback.toDelete /\
  (MAP (\p. (SND p).toDelete) u.contexts =
     MAP (\p. (SND p).toDelete) s.contexts \/
   MAP (\p. (SND p).toDelete) u.contexts =
     s.rollback.toDelete :: MAP (\p. (SND p).toDelete) s.contexts) /\
  (!e. q = INR e ==> e <> SOME Reverted /\
     (e = NONE ==> LENGTH s.contexts < LENGTH u.contexts))
Proof
  Cases_on `op` >> simp[is_call_def, step_inst_def] >> strip_tac
  >>~- ([`step_create _ _ = _`],
        drule_all (BETA_RULE step_create_deletion_projections) >>
        strip_tac >> simp[] >> metis_tac[step_create_exception_class]) >>
  drule_all step_call_deletion_projections >> strip_tac >> simp[] >>
  metis_tac[step_call_exception_not_reverted, step_call_normal_finish_growth,
            prim_recTheory.LESS_REFL]
QED

Theorem step_call_create_body_queue_selector[local]:
  0 < d /\ d <= LENGTH s.contexts /\ is_call op /\
  handle (ignore_bind (step_inst op) (inc_pc_or_jump op)) handle_step s = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    if LENGTH t.contexts < LENGTH s.contexts then
      HD (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s))) ::
      TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
    else if LENGTH t.contexts = LENGTH s.contexts then
      MAP (\rb. rb.toDelete) (active_rollbacks d s)
    else HD (MAP (\rb. rb.toDelete) (active_rollbacks d s)) ::
      MAP (\rb. rb.toDelete) (active_rollbacks d s)
Proof
  strip_tac >>
  `s.contexts <> []` by (strip_tac >> fs[]) >>
  qpat_x_assum `handle _ _ s = _` mp_tac >>
  pure_rewrite_tac[handle_def] >>
  Cases_on `step_inst op s : (unit + vfmExecution$exception option) # execution_state` >>
  rename1 `step_inst op s = (q,u)` >>
  drule_all step_call_create_deletion_control >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `q`) >> simp[ignore_bind_def, bind_def]
  >- (strip_tac >> irule handle_step_same_or_push_queue_selector >>
      metis_tac[]) >>
  `u.contexts <> []` by
    (strip_tac >> fs[] >> Cases_on `s.contexts` >> gvs[]) >>
  Cases_on `inc_pc_or_jump op u : (unit + vfmExecution$exception option) # execution_state` >>
  rename1 `inc_pc_or_jump op u = (q,v)` >>
  `v.contexts <> [] /\
   MAP (\p. (SND p).toDelete) v.contexts =
     MAP (\p. (SND p).toDelete) u.contexts /\
   v.rollback.toDelete = u.rollback.toDelete` by
    (mp_tac inc_pc_or_jump_deletion_exact >>
     pure_rewrite_tac[vfmPreservesTheory.preserves_when_def] >>
     disch_then (qspecl_then [`u`,`q`,`v`] mp_tac) >> simp[]) >>
  `LENGTH v.contexts = LENGTH u.contexts` by metis_tac[LENGTH_MAP] >>
  reverse (Cases_on `q`) >> simp[]
  >- (strip_tac >> drule inc_pc_or_jump_exception_class >> strip_tac >>
      irule handle_step_same_or_push_queue_selector >>
      simp[] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  `MAP (\rb. rb.toDelete) (active_rollbacks d t) =
   if LENGTH t.contexts = LENGTH s.contexts then
     MAP (\rb. rb.toDelete) (active_rollbacks d s)
   else HD (MAP (\rb. rb.toDelete) (active_rollbacks d s)) ::
     MAP (\rb. rb.toDelete) (active_rollbacks d s)` by
    (irule active_deletion_queues_same_or_push >> simp[]) >>
  `LENGTH s.contexts <= LENGTH t.contexts` by
    (`LENGTH t.contexts = LENGTH s.contexts \/
      LENGTH t.contexts = SUC (LENGTH s.contexts)` by
       metis_tac[LENGTH_MAP, LENGTH] >> decide_tac) >>
  simp[]
QED

Theorem step_call_create_queue_selector:
  0 < d /\ d <= LENGTH s.contexts /\
  FLOOKUP (FST (HD s.contexts)).msgParams.parsed
    (FST (HD s.contexts)).pc = SOME op /\
  is_call op /\ step s = (r,t) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    if LENGTH t.contexts < LENGTH s.contexts then
      HD (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s))) ::
      TL (TL (MAP (\rb. rb.toDelete) (active_rollbacks d s)))
    else if LENGTH t.contexts = LENGTH s.contexts then
      MAP (\rb. rb.toDelete) (active_rollbacks d s)
    else HD (MAP (\rb. rb.toDelete) (active_rollbacks d s)) ::
      MAP (\rb. rb.toDelete) (active_rollbacks d s)
Proof
  strip_tac >>
  `s.contexts <> []` by (strip_tac >> fs[]) >>
  irule step_call_create_body_queue_selector >> simp[] >>
  qexistsl [`op`,`r`] >> simp[] >>
  qpat_x_assum `step s = _` mp_tac >>
  simp[step_def, handle_def, get_current_context_def, bind_def, return_def]
QED

Theorem step_queue_suffix[local]:
  0 < d /\ d <= LENGTH s.contexts /\
  erase_toDelete s = erase_toDelete u /\
  MAP (\rb. rb.toDelete) (active_rollbacks d s) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d u)) /\
  step s = (r,t) /\ step u = (q,v) ==>
  MAP (\rb. rb.toDelete) (active_rollbacks d t) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete) (active_rollbacks d v))
Proof
  strip_tac >>
  Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
    (FST (HD s.contexts)).pc`
  >- (irule step_missing_opcode_queue_suffix >> metis_tac[]) >>
  rename1 `FLOOKUP _ _ = SOME op` >>
  Cases_on `op = Stop`
  >- (irule step_stop_queue_suffix >> metis_tac[]) >>
  Cases_on `op = Return \/ op = Revert`
  >- (irule step_return_queue_suffix >> metis_tac[]) >>
  `MAP FST s.contexts = MAP FST u.contexts` by
    (qpat_x_assum `erase_toDelete s = _` mp_tac >>
     simp[erase_toDelete_def, execution_state_component_equality] >>
     strip_tac >>
     qpat_x_assum `MAP _ s.contexts = _`
       (mp_tac o Q.AP_TERM `MAP FST`) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.ELIM_UNCURRY, ETA_THM]) >>
  `LENGTH s.contexts = LENGTH u.contexts /\
   FST (HD s.contexts) = FST (HD u.contexts)` by
    (conj_tac >- metis_tac[LENGTH_MAP] >>
     Cases_on `s.contexts` >> Cases_on `u.contexts` >> gvs[]) >>
  `LENGTH t.contexts = LENGTH v.contexts` by
    (drule step_toDelete >> simp[] >> strip_tac >>
     qpat_x_assum `erase_toDelete t = _` mp_tac >>
     simp[erase_toDelete_def, execution_state_component_equality] >>
     metis_tac[LENGTH_MAP]) >>
  Cases_on `op = SelfDestruct`
  >- (Cases_on `s.contexts` >> Cases_on `u.contexts` >> gvs[] >>
      PairCases_on `h` >> PairCases_on `h'` >>
      qpat_x_assum `erase_toDelete s = _` mp_tac >>
      simp[erase_toDelete_def, execution_state_component_equality,
           rollback_state_component_equality] >> strip_tac >> gvs[] >>
      `d <= LENGTH s.contexts /\ d <= LENGTH u.contexts` by simp[] >>
      qpat_x_assum `step u = _` mp_tac >>
      drule_all step_self_destruct_complete_queue_selector >>
      strip_tac >> disch_tac >>
      qpat_x_assum `step s = _` kall_tac >>
      drule_all step_self_destruct_complete_queue_selector >>
      strip_tac >> gvs[] >>
      Cases_on `LENGTH v.contexts < SUC (LENGTH t'')`
      >- (`v.contexts <> []` by
            (`u.contexts <> []` by simp[] >>
             drule step_preserves_nonempty_contexts >> simp[]) >>
          `t'' <> []` by
            (strip_tac >> gvs[] >> Cases_on `v.contexts` >> gvs[]) >>
          Cases_on `t''` >> gvs[] >>
          rename1 `u.contexts = _::_::ur` >>
          `SUC (SUC (SUC (LENGTH ur))) - MAX 2 d =
           SUC (SUC (SUC (LENGTH ur)) - MAX 2 d)` by
            (gvs[MAX_DEF] >> decide_tac) >>
          rpt IF_CASES_TAC >>
          simp[active_rollbacks_def, MAP_MAP_o, combinTheory.o_DEF, MAP_TL]) >>
      rpt IF_CASES_TAC >>
      simp[active_rollbacks_def, MAP_MAP_o, combinTheory.o_DEF, MAP_TL]) >>
  Cases_on `is_call op`
  >- (drule_at (Pos last) step_call_create_queue_selector >>
      disch_then (qspecl_then [`op`,`d`] mp_tac) >>
      rev_drule_at (Pos last) step_call_create_queue_selector >>
      disch_then (qspecl_then [`op`,`d`] mp_tac) >> gvs[] >>
      Cases_on `LENGTH v.contexts < LENGTH u.contexts`
      >- (simp[] >>
          `u.contexts <> [] /\ v.contexts <> []` by
            (`u.contexts <> []` by (Cases_on `u.contexts` >> gvs[]) >>
             drule step_preserves_nonempty_contexts >> simp[]) >>
          `2 <= LENGTH u.contexts` by
            (Cases_on `v.contexts` >> gvs[] >> decide_tac) >>
          Cases_on `u.contexts` >> gvs[] >> Cases_on `t'` >> gvs[] >>
          `SUC (SUC (SUC (LENGTH t''))) - MAX 2 d =
           SUC (SUC (SUC (LENGTH t'')) - MAX 2 d)` by
            (gvs[MAX_DEF] >> decide_tac) >>
          simp[active_rollbacks_def, MAP_TL, MAP_MAP_o, combinTheory.o_DEF]) >>
      Cases_on `LENGTH v.contexts = LENGTH u.contexts` >> simp[] >>
      Cases_on `u.contexts` >> gvs[active_rollbacks_def, MAP_MAP_o, combinTheory.o_DEF]) >>
  drule_at (Pos last) step_ordinary_queue_selector >>
  disch_then (qspecl_then [`op`,`d`] mp_tac) >>
  rev_drule_at (Pos last) step_ordinary_queue_selector >>
  disch_then (qspecl_then [`op`,`d`] mp_tac) >> gvs[] >>
  Cases_on `LENGTH v.contexts < LENGTH u.contexts` >> simp[] >>
  `u.contexts <> [] /\ v.contexts <> []` by
    (`u.contexts <> []` by (Cases_on `u.contexts` >> gvs[]) >>
     drule step_preserves_nonempty_contexts >> simp[]) >>
  `2 <= LENGTH u.contexts` by
    (Cases_on `v.contexts` >> gvs[] >> decide_tac) >>
  Cases_on `u.contexts` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  `SUC (SUC (SUC (LENGTH t''))) - MAX 2 d =
   SUC (SUC (SUC (LENGTH t'')) - MAX 2 d)` by
    (gvs[MAX_DEF] >> decide_tac) >>
  simp[active_rollbacks_def, MAP_TL, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem call_loop_queue_suffix[local]:
  0 < d ==>
  !x z.
    OWHILE (\(r,s). ISL r /\ LENGTH s.contexts >= d) (step o SND) x = SOME z ==>
    !y. FST x = FST y /\ erase_toDelete (SND x) = erase_toDelete (SND y) /\
      MAP (\rb. rb.toDelete) (active_rollbacks d (SND x)) =
        MAP (\xs. xs ++ b)
          (MAP (\rb. rb.toDelete) (active_rollbacks d (SND y))) ==>
    ?w. OWHILE (\(r,s). ISL r /\ LENGTH s.contexts >= d) (step o SND) y = SOME w /\
      FST z = FST w /\ erase_toDelete (SND z) = erase_toDelete (SND w) /\
      MAP (\rb. rb.toDelete) (active_rollbacks d (SND z)) =
        MAP (\xs. xs ++ b)
          (MAP (\rb. rb.toDelete) (active_rollbacks d (SND w)))
Proof
  strip_tac >> ho_match_mp_tac vfmOriginalStateTheory.OWHILE_simulation >> conj_tac
  >- (qx_gen_tac `x` >> qx_gen_tac `y` >>
      PairCases_on `x` >> PairCases_on `y` >> simp[] >>
      strip_tac >>
      qpat_x_assum `erase_toDelete _ = _` mp_tac >>
      simp[erase_toDelete_def, execution_state_component_equality] >>
      metis_tac[LENGTH_MAP]) >>
  qx_gen_tac `x` >> qx_gen_tac `y` >>
  PairCases_on `x` >> PairCases_on `y` >> simp[] >> strip_tac >>
  Cases_on `step x1` >> Cases_on `step y1` >> simp[] >>
  conj_tac >- metis_tac[step_toDelete, FST, SND] >>
  conj_tac >- metis_tac[step_toDelete, FST, SND] >>
  irule step_queue_suffix >> fs[GREATER_EQ] >> metis_tac[]
QED

Theorem step_push_saved_queue:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts ==>
  t.rollback.toDelete = s.rollback.toDelete /\
  (SND (HD t.contexts)).toDelete = s.rollback.toDelete
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_grow_dispatch >> strip_tac >> gvs[]
  >- (drule_all step_call_deletion_projections >> strip_tac >> gvs[] >>
      Cases_on `t.contexts` >> gvs[]) >>
  drule_all step_create_deletion_projections >> strip_tac >> gvs[] >>
  Cases_on `t.contexts` >> gvs[]
QED

Theorem run_call_queue_suffix:
  s.contexts <> [] /\ s.rollback.toDelete = b /\
  (2 <= LENGTH s.contexts ==> (SND (HD s.contexts)).toDelete = b) /\
  run_call s = SOME (r,t) ==>
  ?v. run_call (erase_toDelete s) = SOME (r,v) /\
    erase_toDelete v = erase_toDelete t /\
    t.rollback.toDelete = v.rollback.toDelete ++ b
Proof
  strip_tac >>
  `0 < LENGTH s.contexts` by (Cases_on `s.contexts` >> gvs[]) >>
  `MAP (\rb. rb.toDelete) (active_rollbacks (LENGTH s.contexts) s) =
    MAP (\xs. xs ++ b) (MAP (\rb. rb.toDelete)
      (active_rollbacks (LENGTH s.contexts) (erase_toDelete s)))` by
    (`MAP (\rb. rb.toDelete)
        (active_rollbacks (LENGTH s.contexts) (erase_toDelete s)) =
        [] :: (if 2 <= LENGTH s.contexts then [[]] else [])` by
       (mp_tac (Q.INST [`s` |-> `erase_toDelete s`] active_deletion_queues_initial) >>
        simp[erase_toDelete_def, MAP_EQ_NIL] >>
        Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> simp[]) >>
     simp[active_deletion_queues_initial] >>
     Cases_on `2 <= LENGTH s.contexts` >> gvs[]) >>
  `LENGTH (erase_toDelete s).contexts = LENGTH s.contexts` by
    simp[erase_toDelete_def] >>
  fs[run_call_def] >>
  drule call_loop_queue_suffix >>
  disch_then (qspec_then `b` mp_tac) >>
  disch_then drule >>
  disch_then (qspec_then `(INL (),erase_toDelete s)` mp_tac) >>
  simp[erase_toDelete_idem] >>
  strip_tac >> PairCases_on `w` >> gvs[] >>
  qpat_x_assum `MAP _ (active_rollbacks _ t) = _`
    (mp_tac o Q.AP_TERM `HD`) >>
  simp[active_rollbacks_def]
QED

Theorem run_call_queue_delta:
  s.contexts <> [] /\ s.rollback.toDelete = b /\
  (2 <= LENGTH s.contexts ==> (SND (HD s.contexts)).toDelete = b) /\
  run_call s = SOME (r,t) ==>
  ?v. run_call (erase_toDelete s) = SOME (r,v) /\
    erase_toDelete v = erase_toDelete t /\
    TAKE (LENGTH t.rollback.toDelete - LENGTH b) t.rollback.toDelete =
      v.rollback.toDelete
Proof
  strip_tac >> drule_all run_call_queue_suffix >> strip_tac >>
  qexists_tac `v` >> simp[rich_listTheory.TAKE_LENGTH_APPEND]
QED
