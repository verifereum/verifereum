Theory vfmAccountDeletion
Ancestors
  combin pair option list rich_list relation arithmetic While
  vfmTypes vfmState vfmContext vfmExecution vfmExecutionProp
  vfmSameFrame vfmRunWithinFrame vfmRunCall vfmStaticCalls vfmDecreasesGas
  vfmStoragePredicates vfmPreserves vfmHandleStep vfmStepLength
  vfmAccountFrame
Libs
  BasicProvers

(* -------------------------------------------------------------------------
 * Deletions.  SELFDESTRUCT schedules its callee for deletion only if the
 * callee is empty in the original accounts (originalAccounts), which only
 * a CREATE at that address changes.  A CREATE needs the address
 * not yet created, which an account with a nonce or code never becomes
 * again within run_call.
 * ------------------------------------------------------------------------- *)

(* Primitive projection boundaries for deletion provenance. *)
Theorem add_to_delete_membership:
  add_to_delete b s = (r, s') ⇒
  (MEM a s'.rollback.toDelete ⇔ a = b ∨ MEM a s.rollback.toDelete)
Proof
  rw[add_to_delete_def, return_def] >> gvs[]
QED

Theorem get_original_accounts:
  s.contexts ≠ [] ⇒
  get_original s = (INL s.originalAccounts, s)
Proof
  simp[get_original_def, return_def]
QED

Theorem set_last_accounts_projections:
  ls ≠ [] ⇒
  MAP FST (set_last_accounts ac ls) = MAP FST ls ∧
  MAP (λp. (SND p).toDelete) (set_last_accounts ac ls) =
    MAP (λp. (SND p).toDelete) ls ∧
  (SND (LAST (set_last_accounts ac ls))).accounts = ac
Proof
  Induct_on `ls` using SNOC_INDUCT >>
  simp[set_last_accounts_def, MAP_SNOC, LAST_SNOC, FRONT_SNOC]
QED

Theorem set_original_projections:
  s.contexts ≠ [] ∧ set_original ac s = (r, s') ⇒
  s'.rollback = s.rollback ∧
  s'.contexts = s.contexts ∧
  MAP FST s'.contexts = MAP FST s.contexts ∧
  MAP (λp. (SND p).toDelete) s'.contexts =
    MAP (λp. (SND p).toDelete) s.contexts ∧
  s'.originalAccounts = ac
Proof
  rw[set_original_def, return_def] >> gvs[] >>
  simp[set_last_accounts_projections]
QED

Theorem cp_deletion_original_projections:
  cp m ∧ s.contexts ≠ [] ∧ m s = (r, s') ⇒
  s'.rollback.toDelete = s.rollback.toDelete ∧
  MAP SND s'.contexts = MAP SND s.contexts ∧
  s'.originalAccounts =
    s.originalAccounts
Proof
  rw[cp_def] >> first_x_assum drule >> simp[] >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

(* ML-only quotations, not new semantic definitions. *)
val deletion_exact = ``λ(s:execution_state) (t:execution_state).
  t.contexts ≠ [] ∧
  MAP (λp. (SND p).toDelete) t.contexts =
    MAP (λp. (SND p).toDelete) s.contexts ∧
  t.originalAccounts = s.originalAccounts ∧
  t.rollback.toDelete = s.rollback.toDelete``;

val deletion_rel = ``λa (s:execution_state) (t:execution_state).
  t.contexts ≠ [] ∧
  MAP (λp. (SND p).toDelete) t.contexts =
    MAP (λp. (SND p).toDelete) s.contexts ∧
  lookup_account a t.originalAccounts =
    lookup_account a s.originalAccounts ∧
  (MEM a t.rollback.toDelete ⇒ MEM a s.rollback.toDelete ∨
    account_empty (lookup_account a s.originalAccounts))``;

Theorem deletion_exact_refl:
  s.contexts ≠ [] ⇒ ^deletion_exact s s
Proof
  simp[]
QED

Theorem deletion_exact_trans:
  ^deletion_exact s t ∧ ^deletion_exact t u ⇒ ^deletion_exact s u
Proof
  simp[]
QED

Theorem deletion_rel_refl:
  s.contexts ≠ [] ⇒ ^deletion_rel a s s
Proof
  simp[]
QED

Theorem deletion_rel_trans:
  ^deletion_rel a s t ∧ ^deletion_rel a t u ⇒ ^deletion_rel a s u
Proof
  simp[] >> metis_tac[]
QED

Theorem deletion_exact_imp_rel:
  ^deletion_exact s t ⇒ ^deletion_rel a s t
Proof
  simp[]
QED

Theorem deletion_exact_nonempty:
  ^deletion_exact s t ⇒ t.contexts ≠ []
Proof
  simp[]
QED

Theorem deletion_rel_nonempty:
  ^deletion_rel a s t ⇒ t.contexts ≠ []
Proof
  simp[]
QED

Theorem cp_deletion_exact:
  cp m ⇒ preserves_when (λs. s.contexts ≠ []) ^deletion_exact m
Proof
  rw[preserves_when_def, cp_def] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >>
  rename1 `s.contexts = h::tail` >> Cases_on `tail` >> gvs[]
QED

Theorem update_accounts_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (update_accounts f)
Proof
  rw[preserves_when_def, update_accounts_def, return_def] >> gvs[]
QED

Theorem preserves_deletion_exact_imp_rel:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact m ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) m
Proof
  rw[preserves_when_def] >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[]
QED

Theorem deletion_exact_bind:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  (∀x. preserves_when (λs. s.contexts ≠ []) ^deletion_exact (f x)) ⇒
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (bind g f)
Proof
  strip_tac >> irule preserves_when_bind >>
  simp[deletion_exact_trans]
QED

Theorem deletion_rel_bind:
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) g ∧
  (∀x. preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (f x)) ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (bind g f)
Proof
  strip_tac >> irule preserves_when_bind >>
  simp[deletion_rel_trans] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem deletion_rel_ignore_bind:
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) g ∧
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) f ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (ignore_bind g f)
Proof
  simp[ignore_bind_def] >> strip_tac >>
  irule (SRULE [] deletion_rel_bind) >> simp[]
QED

Theorem deletion_rel_bind_get_original:
  (∀s r t. s.contexts ≠ [] ∧
    f (s.originalAccounts) s = (r,t) ⇒
    ^deletion_rel a s t) ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a)
    (bind get_original f)
Proof
  rw[preserves_when_def, bind_def, get_original_def, return_def] >>
  gvs[] >> first_x_assum drule_all >> simp[]
QED

Theorem deletion_rel_bind_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  (∀x. preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (f x)) ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (bind g f)
Proof
  strip_tac >> irule deletion_rel_bind >> simp[] >>
  irule (SRULE [] preserves_deletion_exact_imp_rel) >> simp[]
QED

Theorem deletion_rel_ignore_bind_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) f ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (ignore_bind g f)
Proof
  strip_tac >> irule deletion_rel_ignore_bind >> simp[] >>
  irule (SRULE [] preserves_deletion_exact_imp_rel) >> simp[]
QED

Theorem step_self_destruct_deletion_rel:
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) step_self_destruct
Proof
  simp[step_self_destruct_def] >>
  irule (SRULE [] deletion_rel_bind_exact) >>
  simp[cp_deletion_exact] >> gen_tac >>
  irule (SRULE [] deletion_rel_bind_exact) >>
  simp[cp_deletion_exact] >> gen_tac >>
  irule (SRULE [] deletion_rel_bind_exact) >>
  simp[cp_deletion_exact] >> gen_tac >>
  irule (SRULE [] deletion_rel_ignore_bind_exact) >>
  simp[cp_deletion_exact] >>
  irule (SRULE [] deletion_rel_bind_exact) >>
  simp[cp_deletion_exact] >> gen_tac >>
  irule (SRULE [] deletion_rel_ignore_bind_exact) >>
  simp[cp_deletion_exact] >>
  irule (SRULE [] deletion_rel_ignore_bind_exact) >>
  simp[cp_deletion_exact] >>
  irule (SRULE [] deletion_rel_ignore_bind_exact) >>
  simp[update_accounts_deletion_exact] >>
  irule (SRULE [] deletion_rel_bind_get_original) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  gvs[ignore_bind_def, bind_def, update_accounts_def,
      add_to_delete_def, return_def, finish_def, fail_def,
      COND_RATOR, AllCaseEqs()] >> metis_tac[]
QED

Theorem deletion_exact_ignore_bind:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact f ⇒
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (ignore_bind g f)
Proof
  simp[ignore_bind_def] >> strip_tac >> irule deletion_exact_bind >> simp[]
QED

Theorem write_storage_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (write_storage a k v)
Proof
  simp[write_storage_def, update_accounts_deletion_exact]
QED

Theorem write_transient_storage_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact
    (write_transient_storage a k v)
Proof
  simp[write_transient_storage_def] >>
  irule deletion_exact_bind >> simp[cp_deletion_exact] >> gen_tac >>
  rw[preserves_when_def, set_tStorage_def, return_def] >> gvs[]
QED

Theorem push_logs_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (push_logs logs)
Proof
  rw[preserves_when_def, push_logs_def, bind_def, get_current_context_def,
     set_current_context_def, return_def] >>
  Cases_on `s.contexts` >> gvs[] >>
  rename1 `s.contexts = h::tail` >> Cases_on `tail` >> gvs[]
QED

Theorem step_sstore_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (step_sstore transient)
Proof
  simp[step_sstore_def] >>
  irule deletion_exact_bind >> simp[cp_deletion_exact] >> gen_tac >>
  irule deletion_exact_bind >> simp[cp_deletion_exact] >> gen_tac >>
  irule deletion_exact_ignore_bind >> simp[cp_deletion_exact] >>
  irule deletion_exact_ignore_bind >> simp[cp_deletion_exact] >>
  Cases_on `transient` >>
  simp[write_storage_deletion_exact, write_transient_storage_deletion_exact]
QED

Theorem step_log_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (step_log n)
Proof
  simp[step_log_def] >>
  irule deletion_exact_bind >> simp[cp_deletion_exact] >> gen_tac >>
  irule deletion_exact_bind >> simp[cp_deletion_exact] >> gen_tac >>
  irule deletion_exact_ignore_bind >> simp[cp_deletion_exact] >>
  irule deletion_exact_ignore_bind >> simp[cp_deletion_exact] >>
  irule deletion_exact_ignore_bind >> simp[cp_deletion_exact] >>
  irule deletion_exact_bind >> simp[cp_deletion_exact] >> gen_tac >>
  irule deletion_exact_bind >>
  simp[cp_deletion_exact, push_logs_deletion_exact]
QED

Theorem step_inst_deletion_exact:
  op ≠ SelfDestruct ∧ op ≠ Create ∧ op ≠ Create2 ∧
  op ≠ Call ∧ op ≠ CallCode ∧ op ≠ DelegateCall ∧ op ≠ StaticCall ⇒
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (step_inst op)
Proof
  strip_tac >>
  Cases_on `op = SStore` >-
    gvs[step_inst_def, step_sstore_deletion_exact] >>
  Cases_on `op = TStore` >-
    gvs[step_inst_def, step_sstore_deletion_exact] >>
  Cases_on `∃n. op = Log n` >-
    gvs[step_inst_def, step_log_deletion_exact] >>
  irule cp_deletion_exact >> irule cp_step_inst_non_call >> gvs[]
QED

Theorem inc_pc_or_jump_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (inc_pc_or_jump op)
Proof
  irule cp_deletion_exact >> simp[]
QED

Theorem step_self_destruct_deletion_provenance:
  s.contexts ≠ [] ∧ step_self_destruct s = (r,t) ⇒
  MAP (λp. (SND p).toDelete) t.contexts =
    MAP (λp. (SND p).toDelete) s.contexts ∧
  lookup_account a t.originalAccounts =
    lookup_account a s.originalAccounts ∧
  (MEM a t.rollback.toDelete ⇒ MEM a s.rollback.toDelete ∨
    account_empty (lookup_account a s.originalAccounts))
Proof
  mp_tac step_self_destruct_deletion_rel >>
  simp[preserves_when_def] >> metis_tac[]
QED

Theorem set_last_accounts_length:
  ls ≠ [] ⇒ LENGTH (set_last_accounts ac ls) = LENGTH ls
Proof
  Induct_on `ls` using SNOC_INDUCT >>
  simp[set_last_accounts_def, FRONT_SNOC]
QED

Theorem proceed_create_deletion_projections:
  s.contexts ≠ [] ∧
  proceed_create sender address value code gas s = (r,t) ⇒
  t.rollback.toDelete = s.rollback.toDelete ∧
  MAP (λp. (SND p).toDelete) t.contexts =
    s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  t.originalAccounts =
    update_account address empty_account_state
      s.originalAccounts
Proof
  strip_tac >> qhdtm_x_assum `proceed_create` mp_tac >>
  simp[proceed_create_def, ignore_bind_def, bind_def,
       update_accounts_def, get_rollback_def, get_original_def,
       set_original_def, push_context_def, return_def] >>
  strip_tac >> gvs[]
QED

Theorem proceed_call_deletion_projections:
  s.contexts ≠ [] ∧
  proceed_call op sender address value argsOffset argsSize code stipend
    outputTo s = (r,t) ⇒
  t.rollback.toDelete = s.rollback.toDelete ∧
  MAP (λp. (SND p).toDelete) t.contexts =
    s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  t.originalAccounts = s.originalAccounts
Proof
  strip_tac >> qhdtm_x_assum `proceed_call` mp_tac >>
  simp[proceed_call_def, bind_def, ignore_bind_def, get_rollback_def,
       read_memory_def, get_current_context_def, return_def] >>
  Cases_on `op ≠ CallCode ∧ 0 < value` >>
  simp[update_accounts_def, return_def, get_caller_def, get_value_def,
       get_static_def, get_current_context_def, bind_def,
       push_context_def, ignore_bind_def] >>
    qmatch_goalsub_abbrev_tac `(if _ then _ else _) ss` >>
  qmatch_goalsub_abbrev_tac `m ss = _` >> strip_tac >>
  `ss.contexts ≠ []` by simp[Abbr `ss`] >>
  `preserves_when (λs. s.contexts ≠ []) ^deletion_exact m` by
    (irule cp_deletion_exact >> simp[Abbr `m`] >>
     Cases_on `fIN address precompile_addresses` >> simp[]) >>
  pop_assum mp_tac >> simp[preserves_when_def] >>
  disch_then drule >> disch_then drule >> strip_tac >>
  gvs[] >>
  `LENGTH t.contexts = LENGTH ss.contexts` by
    metis_tac[LENGTH_MAP] >>
  simp[Abbr `ss`, LAST_DEF]
QED


val deletion_call = ``λ(s:execution_state) (t:execution_state).
  t.contexts ≠ [] ∧
  t.rollback.toDelete = s.rollback.toDelete ∧
  t.originalAccounts = s.originalAccounts ∧
  (MAP (λp. (SND p).toDelete) t.contexts =
     MAP (λp. (SND p).toDelete) s.contexts ∨
   MAP (λp. (SND p).toDelete) t.contexts =
     s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts)``;

Theorem deletion_call_bind_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  (∀x. preserves_when (λs. s.contexts ≠ []) ^deletion_call (f x)) ⇒
  preserves_when (λs. s.contexts ≠ []) ^deletion_call (bind g f)
Proof
  rw[preserves_when_def, bind_def, AllCaseEqs()] >>
  rpt (first_x_assum drule) >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem cp_deletion_call:
  cp m ⇒ preserves_when (λs. s.contexts ≠ []) ^deletion_call m
Proof
  strip_tac >> drule cp_deletion_exact >>
  simp[preserves_when_def] >> metis_tac[]
QED

Theorem proceed_call_deletion_call:
  preserves_when (λs. s.contexts ≠ []) ^deletion_call
    (proceed_call op sender address value argsOffset argsSize code stipend outputTo)
Proof
  rw[preserves_when_def] >> drule_all proceed_call_deletion_projections >>
  strip_tac >> Cases_on `t.contexts` >> gvs[]
QED

Theorem deletion_call_ignore_bind_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  preserves_when (λs. s.contexts ≠ []) ^deletion_call f ⇒
  preserves_when (λs. s.contexts ≠ []) ^deletion_call (ignore_bind g f)
Proof
  simp[ignore_bind_def] >> strip_tac >>
  irule deletion_call_bind_exact >> simp[]
QED

Theorem step_call_deletion_call:
  preserves_when (λs. s.contexts ≠ []) ^deletion_call (step_call op)
Proof
  simp[step_call_def] >>
  irule deletion_call_bind_exact >> simp[cp_deletion_exact] >> gen_tac >>
  pairarg_tac >> simp[] >>
  irule deletion_call_bind_exact >> simp[cp_deletion_exact] >> gen_tac >>
  irule deletion_call_bind_exact >> simp[cp_deletion_exact] >> gen_tac >>
  irule deletion_call_bind_exact >> simp[cp_deletion_exact] >> gen_tac >>
  irule deletion_call_bind_exact >> reverse conj_tac >-
    (irule cp_deletion_exact >>
     CASE_TAC >> simp[]) >>
  qx_gen_tac `codecost` >> PairCases_on `codecost` >>
  simp[] >> irule deletion_call_bind_exact >>
  simp[cp_deletion_exact] >> gen_tac >>
  pairarg_tac >> simp[] >>
  irule deletion_call_ignore_bind_exact >> simp[cp_deletion_exact] >>
  irule deletion_call_ignore_bind_exact >> conj_tac >-
    (irule cp_deletion_exact >> IF_CASES_TAC >> simp[]) >>
  irule deletion_call_ignore_bind_exact >> simp[cp_deletion_exact] >>
  irule deletion_call_bind_exact >> simp[cp_deletion_exact] >> gen_tac >>
  IF_CASES_TAC >- (irule cp_deletion_call >> simp[]) >>
  irule deletion_call_ignore_bind_exact >> simp[cp_deletion_exact] >>
  irule deletion_call_bind_exact >> simp[cp_deletion_exact] >> gen_tac >>
  IF_CASES_TAC >- (irule cp_deletion_call >> simp[]) >>
  simp[proceed_call_deletion_call]
QED

Theorem step_call_deletion_projections:
  s.contexts ≠ [] ∧ step_call op s = (r,t) ⇒
  t.rollback.toDelete = s.rollback.toDelete ∧
  t.originalAccounts = s.originalAccounts ∧
  ((MAP (λp. (SND p).toDelete) t.contexts =
      MAP (λp. (SND p).toDelete) s.contexts ∧
    LENGTH t.contexts = LENGTH s.contexts) ∨
   (MAP (λp. (SND p).toDelete) t.contexts =
      s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts ∧
    LENGTH t.contexts = SUC (LENGTH s.contexts)))
Proof
  mp_tac step_call_deletion_call >>
  simp[preserves_when_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  metis_tac[LENGTH_MAP, LENGTH]
QED

Theorem fixed_accounts_bind_cp:
  cp g ∧
  (∀x. preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    R (f x)) ∧
  (∀s t. s.contexts ≠ [] ∧ cp_rel s t ⇒ R s t) ∧
  (∀s t u. s.contexts ≠ [] ∧ cp_rel s t ∧ R t u ⇒ R s u) ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    R (bind g f)
Proof
  simp[cp_eq_preserves_when, preserves_when_def] >> strip_tac >>
  rw[bind_def, AllCaseEqs()] >>
  qpat_x_assum `∀s r t. g s = _ ∧ _ ⇒ _` drule_all >> strip_tac >>
  rename1 `cp_rel s mid` >>
  `mid.contexts ≠ []` by metis_tac[cp_rel_contexts_ne] >>
  `mid.rollback.accounts = s.rollback.accounts` by gvs[cp_rel_def] >>
  metis_tac[]
QED

Theorem fixed_accounts_ignore_bind_cp:
  cp g ∧
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A) R f ∧
  (∀s t. s.contexts ≠ [] ∧ cp_rel s t ⇒ R s t) ∧
  (∀s t u. s.contexts ≠ [] ∧ cp_rel s t ∧ R t u ⇒ R s u) ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    R (ignore_bind g f)
Proof
  simp[ignore_bind_def] >> strip_tac >>
  irule fixed_accounts_bind_cp >> simp[] >> metis_tac[]
QED

Theorem fixed_accounts_bind_get_accounts:
  (∀A. preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (R A) (f A)) ⇒
  preserves_when (λs. s.contexts ≠ [])
    (λs t. R s.rollback.accounts s t) (bind get_accounts f)
Proof
  rw[preserves_when_def, bind_def, get_accounts_def, return_def] >>
  first_x_assum drule >> simp[]
QED

val deletion_create = ``λA (s:execution_state) (t:execution_state).
  t.contexts ≠ [] ∧ t.rollback.toDelete = s.rollback.toDelete ∧
  ((MAP (λp. (SND p).toDelete) t.contexts =
      MAP (λp. (SND p).toDelete) s.contexts ∧
    LENGTH t.contexts = LENGTH s.contexts ∧
    t.originalAccounts = s.originalAccounts) ∨
   (∃b. MAP (λp. (SND p).toDelete) t.contexts =
          s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts ∧
        LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
        t.originalAccounts =
          update_account b empty_account_state s.originalAccounts ∧
        (lookup_account b A).nonce = 0 ∧ NULL (lookup_account b A).code))``;

Theorem cp_rel_deletion_exact:
  s.contexts ≠ [] ∧ cp_rel s t ⇒ ^deletion_exact s t
Proof
  rw[cp_rel_def] >> Cases_on `s.contexts` >> gvs[] >>
  rename1 `s.contexts = h::tail` >> Cases_on `tail` >> gvs[]
QED

Theorem deletion_exact_imp_create:
  ^deletion_exact s t ⇒ ^deletion_create A s t
Proof
  simp[] >> strip_tac >> simp[] >>
  metis_tac[LENGTH_MAP]
QED

Theorem deletion_create_transport:
  ^deletion_exact s t ∧ ^deletion_create A t u ⇒ ^deletion_create A s u
Proof
  simp[] >> strip_tac >>
  `LENGTH t.contexts = LENGTH s.contexts` by metis_tac[LENGTH_MAP] >>
  gvs[] >> metis_tac[]
QED

Theorem cp_rel_deletion_create:
  s.contexts ≠ [] ∧ cp_rel s t ⇒ ^deletion_create A s t
Proof
  metis_tac[cp_rel_deletion_exact, deletion_exact_imp_create]
QED

Theorem cp_rel_deletion_create_transport:
  s.contexts ≠ [] ∧ cp_rel s t ∧ ^deletion_create A t u ⇒
  ^deletion_create A s u
Proof
  simp[] >> strip_tac >> drule_all cp_rel_deletion_exact >>
  simp[] >> strip_tac >>
  `LENGTH t.contexts = LENGTH s.contexts` by metis_tac[LENGTH_MAP] >>
  gvs[] >> metis_tac[]
QED

Theorem deletion_create_bind_cp:
  cp g ∧
  (∀x. preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) (f x)) ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) (bind g f)
Proof
  strip_tac >> irule fixed_accounts_bind_cp >>
  asm_rewrite_tac[cp_rel_deletion_create, cp_rel_deletion_create_transport]
QED

Theorem deletion_create_ignore_bind_cp:
  cp g ∧
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) f ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) (ignore_bind g f)
Proof
  simp[ignore_bind_def] >> strip_tac >>
  irule (SRULE [] deletion_create_bind_cp) >> simp[]
QED

Theorem deletion_exact_preserves_create:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact m ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) m
Proof
  rw[preserves_when_def] >> first_x_assum drule_all >>
  metis_tac[deletion_exact_imp_create]
QED

Theorem proceed_create_deletion_create:
  ¬account_already_created (lookup_account address A) ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) (proceed_create sender address value code gas)
Proof
  strip_tac >> rewrite_tac[preserves_when_def] >>
  map_every qx_gen_tac [`s`, `r`, `t`] >> strip_tac >> gvs[] >>
  drule_all proceed_create_deletion_projections >> strip_tac >>
  `t.contexts ≠ []` by (Cases_on `t.contexts` >> gvs[]) >>
  simp[] >> qexists_tac `address` >>
  gvs[account_already_created_def]
QED

Theorem fixed_accounts_get_accounts_eq:
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A) R (f A) ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A) R
    (bind get_accounts f)
Proof
  rw[preserves_when_def, bind_def, get_accounts_def, return_def] >>
  first_x_assum drule >> simp[]
QED

Theorem abort_create_exists_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact
    (abort_create_exists sender)
Proof
  simp[abort_create_exists_def, ignore_bind_def] >>
  irule deletion_exact_bind >>
  simp[update_accounts_deletion_exact] >>
  irule cp_deletion_exact >> simp[]
QED

Theorem step_create_deletion_create:
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) (step_create two)
Proof
  simp[step_create_def] >>
  irule (SRULE [] deletion_create_bind_cp) >> simp[] >> gen_tac >>
  irule (SRULE [] deletion_create_bind_cp) >> simp[] >> gen_tac >>
  irule (SRULE [] deletion_create_ignore_bind_cp) >> simp[] >>
  irule (SRULE [] deletion_create_ignore_bind_cp) >> simp[] >>
  irule (SRULE [] deletion_create_bind_cp) >> simp[] >> gen_tac >>
  irule (SRULE [] deletion_create_bind_cp) >> simp[] >> gen_tac >>
  irule fixed_accounts_get_accounts_eq >>
  simp[] >>
  irule (SRULE [] deletion_create_ignore_bind_cp) >> simp[] >>
  irule (SRULE [] deletion_create_bind_cp) >> simp[] >> gen_tac >>
  irule (SRULE [] deletion_create_ignore_bind_cp) >> simp[] >>
  irule (SRULE [] deletion_create_ignore_bind_cp) >> simp[] >>
  irule (SRULE [] deletion_create_ignore_bind_cp) >> simp[] >>
  irule (SRULE [] deletion_create_bind_cp) >> simp[] >> gen_tac >>
  IF_CASES_TAC >-
    (irule (SRULE [] deletion_exact_preserves_create) >>
     irule cp_deletion_exact >> simp[]) >>
  irule (SRULE [] deletion_create_ignore_bind_cp) >> simp[] >>
  irule (SRULE [] deletion_create_ignore_bind_cp) >> simp[] >>
  IF_CASES_TAC >-
    (irule (SRULE [] deletion_exact_preserves_create) >>
     simp[abort_create_exists_deletion_exact]) >>
  irule (SRULE [] proceed_create_deletion_create) >> simp[]
QED

Theorem step_create_deletion_projections:
  s.contexts ≠ [] ∧ step_create two s = (r,t) ⇒
  ^deletion_create s.rollback.accounts s t
Proof
  strip_tac >>
  mp_tac (Q.INST [`A` |-> `s.rollback.accounts`]
    step_create_deletion_create) >>
  simp[preserves_when_def] >> disch_then drule >> simp[]
QED

Theorem handle_create_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (handle_create e)
Proof
  simp[handle_create_def] >>
  irule deletion_exact_bind >> simp[cp_deletion_exact] >> gen_tac >>
  irule deletion_exact_bind >> simp[cp_deletion_exact] >>
  qx_gen_tac `output` >> Cases_on `e` >> Cases_on `output` >>
  simp[cp_deletion_exact, ignore_bind_def] >>
  irule deletion_exact_bind >> simp[cp_deletion_exact] >>
  irule deletion_exact_bind >> simp[cp_deletion_exact] >>
  irule deletion_exact_bind >> simp[cp_deletion_exact] >>
  irule deletion_exact_bind >>
  simp[update_accounts_deletion_exact, cp_deletion_exact]
QED

Theorem pop_context_deletion_projections:
  2 ≤ LENGTH s.contexts ∧
  pop_and_incorporate_context success s = (r,t) ⇒
  t.contexts ≠ [] ∧
  t.originalAccounts = s.originalAccounts ∧
  (t.rollback.toDelete = s.rollback.toDelete ∨
   t.rollback.toDelete = (SND (HD s.contexts)).toDelete) ∧
  LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
  MAP (λp. (SND p).toDelete) t.contexts =
    TL (MAP (λp. (SND p).toDelete) s.contexts)
Proof
  Cases_on `s.contexts` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  PairCases_on `h` >> PairCases_on `h'` >>
  simp[pop_and_incorporate_context_def, bind_def, ignore_bind_def,
       get_gas_left_def, get_current_context_def, return_def,
       pop_context_def, unuse_gas_def, assert_def, fail_def,
       set_current_context_def, push_logs_def, update_gas_refund_def,
       set_rollback_def] >>
  Cases_on `success` >>
  simp[bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, set_rollback_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> Cases_on `t''` >> gvs[]
QED

Theorem handle_exception_deletion_projections:
  s.contexts ≠ [] ∧ handle_exception e s = (r,t) ⇒
  t.contexts ≠ [] ∧
  t.originalAccounts = s.originalAccounts ∧
  (t.rollback.toDelete = s.rollback.toDelete ∨
   (2 ≤ LENGTH s.contexts ∧
    t.rollback.toDelete = (SND (HD s.contexts)).toDelete)) ∧
  ((LENGTH t.contexts = LENGTH s.contexts ∧
    MAP (λp. (SND p).toDelete) t.contexts =
      MAP (λp. (SND p).toDelete) s.contexts) ∨
   (2 ≤ LENGTH s.contexts ∧
    LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
    MAP (λp. (SND p).toDelete) t.contexts =
      TL (MAP (λp. (SND p).toDelete) s.contexts)))
Proof
  Cases_on `s.contexts` >> simp[] >> PairCases_on `h` >>
  Cases_on `t'` >> simp[]
  >- (Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
      simp[handle_exception_def, bind_def, ignore_bind_def,
           get_gas_left_def, get_current_context_def, return_def,
           consume_gas_def, set_return_data_def, set_current_context_def,
           get_num_contexts_def, reraise_def, assert_def, fail_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      Cases_on `h0.msgParams.gasLimit - h0.gasUsed + h0.gasUsed ≤ h0.msgParams.gasLimit` >>
      gvs[]) >>
  PairCases_on `h` >>
  Cases_on `h0.msgParams.outputTo` >>
  Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  simp[handle_exception_def, bind_def, ignore_bind_def,
       get_gas_left_def, get_current_context_def, return_def,
       consume_gas_def, set_return_data_def, set_current_context_def,
       get_num_contexts_def, get_return_data_def, get_output_to_def,
       reraise_def, assert_def, fail_def,
       inc_pc_def, push_stack_def, write_memory_def,
       pop_and_incorporate_context_def, pop_context_def,
       set_rollback_def, unuse_gas_def,
       update_gas_refund_def, push_logs_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> Cases_on `t''` >> gvs[AllCaseEqs()]
QED

Theorem handle_step_deletion_projections:
  s.contexts ≠ [] ∧ handle_step e s = (r,t) ⇒
  t.contexts ≠ [] ∧
  t.originalAccounts = s.originalAccounts ∧
  (t.rollback.toDelete = s.rollback.toDelete ∨
   (2 ≤ LENGTH s.contexts ∧
    t.rollback.toDelete = (SND (HD s.contexts)).toDelete)) ∧
  ((LENGTH t.contexts = LENGTH s.contexts ∧
    MAP (λp. (SND p).toDelete) t.contexts =
      MAP (λp. (SND p).toDelete) s.contexts) ∨
   (2 ≤ LENGTH s.contexts ∧
    LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
    MAP (λp. (SND p).toDelete) t.contexts =
      TL (MAP (λp. (SND p).toDelete) s.contexts)))
Proof
  strip_tac >> qhdtm_x_assum `handle_step` mp_tac >>
  simp[handle_step_def] >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[]) >>
  simp[handle_def] >>
  strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR) >>
  simp[] >> strip_tac >>
  drule_all vfmHandleStepTheory.handle_create_preserves_tl_and_snd_hd >> strip_tac >>
  drule_all vfmHandleStepTheory.handle_create_preserves_length >> strip_tac >>
  mp_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_deletion_exact) >>
  simp[preserves_when_def] >> disch_then (drule_all_then strip_assume_tac) >>
  drule_all handle_exception_deletion_projections >>
  strip_tac >> gvs[]
QED

(* Account-protection boundaries. *)
Theorem collision_free_nonce_code:
  ¬account_already_created acc ⇒ acc.nonce = 0 ∧ acc.code = []
Proof
  simp[account_already_created_def, NULL_EQ]
QED

(* increment_nonce_lookup and increment_nonce_code are shared upstream. *)

(* deposit_code_nonce and deposit_code_other are shared in RunCall. *)

(* proceed_create_nonce_certificate is shared in vfmStoragePredicates. *)

val push_post = ``λQ (m:execution_state -> ('a + exception option) # execution_state). ∀s r t.
  m s = (r,t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒ Q s t``;

Theorem push_post_bind:
  preserves R g ∧
  (∀s u. R s u ⇒ (s.contexts ≠ [] ⇒ u.contexts ≠ []) ∧
                       LENGTH u.contexts = LENGTH s.contexts) ∧
  (∀s u t. R s u ∧ Q u t ⇒ Q s t) ∧
  (∀x. ^push_post Q (f x)) ⇒
  ^push_post Q (bind g f)
Proof
  rw[preserves_def, bind_def] >> gvs[AllCaseEqs()] >>
  qpat_x_assum `∀s r s'. g s = (r,s') ⇒ _` drule >> strip_tac >>
  qpat_assum `∀s u. R s u ⇒ _` drule >> strip_tac >> fs[] >>
  qpat_x_assum `∀s u t. R s u ∧ Q u t ⇒ _` irule >>
  goal_assum (drule_at Any) >> first_x_assum irule >>
  qpat_x_assum `∀s u. R s u ⇒ _` drule >> simp[] >> metis_tac[]
QED

Theorem push_post_bind_psf:
  preserves_same_frame g ∧
  (∀x. ^push_post (λs t. P t) (f x)) ⇒
  ^push_post (λs t. P t) (bind g f)
Proof
  rw[preserves_same_frame_def, bind_def] >> gvs[AllCaseEqs()] >>
  qpat_x_assum `∀s r s'. g s = (r,s') ∧ _ ⇒ _` drule >>
  simp[] >> strip_tac >>
  gvs[same_frame_rel_def] >>
  first_x_assum irule >>
  qexistsl [`r`, `s''`, `x`] >> simp[] >>
  Cases_on `s''.contexts` >> gvs[]
QED

Theorem push_post_ignore_bind_psf:
  preserves_same_frame g ∧ ^push_post (λs t. P t) f ⇒
  ^push_post (λs t. P t) (ignore_bind g f)
Proof
  simp[ignore_bind_def] >> strip_tac >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem push_post_cond:
  ^push_post Q f ∧ ^push_post Q g ⇒
  ^push_post Q (if b then f else g)
Proof
  Cases_on `b` >> simp[]
QED

Theorem push_post_nongrowing:
  (∀s r t. m s = (r,t) ∧ s.contexts ≠ [] ⇒
    LENGTH t.contexts ≤ LENGTH s.contexts) ⇒ ^push_post Q m
Proof
  rw[] >> first_x_assum drule >> simp[]
QED

val push_post_unit = inst [alpha |-> ``:unit``] push_post;

Theorem proceed_create_nonce_certificate_prefix:
  preserves_same_frame g ⇒
  ^push_post_unit (λs t.
    0 < (lookup_account address t.rollback.accounts).nonce ∧
    (FST (HD t.contexts)).msgParams.outputTo = Code address)
    (bind g (λx. proceed_create sender address value code gas))
Proof
  strip_tac >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  metis_tac[proceed_create_nonce_certificate]
QED

Theorem step_create_growth_nonce_certificate:
  ^push_post_unit (λs t. ∀b.
    (FST (HD t.contexts)).msgParams.outputTo = Code b ⇒
    0 < (lookup_account b t.rollback.accounts).nonce) (step_create two)
Proof
  simp[step_create_def, ignore_bind_def] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  IF_CASES_TAC
  >- (rpt strip_tac >> drule_all vfmStepLengthTheory.abort_unuse_length >> simp[]) >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  IF_CASES_TAC
  >- (rpt strip_tac >> drule_all vfmStepLengthTheory.abort_create_exists_length >> simp[]) >>
  rpt strip_tac >> drule_all proceed_create_nonce_certificate >>
  strip_tac >> gvs[]
QED

(* proceed_call_memory_output is shared in RunCall. *)

Theorem step_call_growth_not_code:
  ^push_post_unit (λs t. ∀b.
    (FST (HD t.contexts)).msgParams.outputTo ≠ Code b) (step_call op)
Proof
  simp[step_call_def, ignore_bind_def] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  pairarg_tac >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  Cases >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  pairarg_tac >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  IF_CASES_TAC
  >- (rpt strip_tac >>
      mp_tac (Q.INST [`n` |-> `stipend`] preserves_same_frame_abort_call_value) >>
      rewrite_tac[preserves_same_frame_def] >>
      disch_then drule >> simp[] >> strip_tac >>
      gvs[same_frame_rel_def]) >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >>
  ho_match_mp_tac (SRULE [] push_post_bind_psf) >> simp[] >> gen_tac >>
  IF_CASES_TAC
  >- (rpt strip_tac >> drule_all vfmStepLengthTheory.abort_unuse_length >> simp[]) >>
  rpt strip_tac >> drule_all proceed_call_memory_output >> simp[]
QED

(* Nonce/code transport before the return-code deposit boundary. *)
val nonce_code_rel = ``λa (s:execution_state) (t:execution_state).
  (lookup_account a s.rollback.accounts).nonce ≤
    (lookup_account a t.rollback.accounts).nonce ∧
  (lookup_account a t.rollback.accounts).code =
    (lookup_account a s.rollback.accounts).code``;

(* Generic nonce/code transport theorems are provided by vfmRunCallTheory. *)

(* Old-snapshot lookup transport is shared in RunCall. *)

(* step_growth_nonce_code is shared upstream in vfmRunCallTheory. *)

(* Saved-head nonce/code interfaces are shared in RunCall. *)

(* step_growth_nonce_certificate is shared in RunCall. *)

(* Same-frame and handle_create protection boundaries are shared in RunCall. *)

(* Depth-indexed bookkeeping for continuing run_call states.  Only the
 * newly pushed snapshots need account protection.  The initial saved head
 * can be restored at the terminal pop, but its deletion list is accessible. *)
val deletion_saved_absent = ``λn a (s:execution_state).
  ∀i. i < (if n = 1 then LENGTH s.contexts - 1
           else LENGTH s.contexts - n + 1) ⇒
    ¬MEM a (SND (EL i s.contexts)).toDelete``;

val deletion_saved_protected = ``λn a (s:execution_state).
  ∀i. i < LENGTH s.contexts - n ⇒
    (lookup_account a (SND (EL i s.contexts)).accounts).nonce ≠ 0 ∨
    ¬NULL (lookup_account a (SND (EL i s.contexts)).accounts).code``;

val deletion_creation_certificate = ``λn a (s:execution_state).
  ∀i. i < LENGTH s.contexts - n ∧
    (FST (EL i s.contexts)).msgParams.outputTo = Code a ⇒
    0 < (lookup_account a s.rollback.accounts).nonce ∧
    ∀j. j < i ⇒
      0 < (lookup_account a (SND (EL j s.contexts)).accounts).nonce``;

val deletion_run_inv = ``λn a original (s:execution_state).
  wf_state s ∧ n ≤ LENGTH s.contexts ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
    ¬NULL (lookup_account a s.rollback.accounts).code) ∧
  lookup_account a s.originalAccounts = original ∧
  ¬MEM a s.rollback.toDelete ∧
  ^deletion_saved_absent n a s ∧
  ^deletion_saved_protected n a s ∧
  ^deletion_creation_certificate n a s``;

Theorem deletion_run_inv_initial:
  wf_state s ∧ ¬MEM a s.rollback.toDelete ∧
  ¬(2 ≤ LENGTH s.contexts ∧ MEM a (SND (HD s.contexts)).toDelete) ∧
  ¬((lookup_account a s.rollback.accounts).nonce = 0 ∧
     NULL (lookup_account a s.rollback.accounts).code) ⇒
  ^deletion_run_inv (LENGTH s.contexts) a
    (lookup_account a s.originalAccounts) s
Proof
  simp[] >> strip_tac >> simp[] >>
  `s.contexts ≠ []` by gvs[wf_state_def] >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `t` >> gvs[EL]
QED

Theorem deletion_head_creation_certificate:
  ^deletion_creation_certificate n a s ∧ n < LENGTH s.contexts ∧
  (FST (HD s.contexts)).msgParams.outputTo = Code a ⇒
  0 < (lookup_account a s.rollback.accounts).nonce
Proof
  simp[] >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[EL] 
QED

Theorem deletion_pop_at_initial_depth_terminal:
  n = LENGTH s.contexts ∧ LENGTH t.contexts < LENGTH s.contexts ⇒
  ¬(n ≤ LENGTH t.contexts)
Proof
  simp[]
QED

Theorem deletion_saved_absent_push:
  0 < n ∧ n ≤ LENGTH s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  ^deletion_saved_absent n a s ∧
  ¬MEM a (SND (HD t.contexts)).toDelete ∧
  (∀i. i < LENGTH s.contexts ⇒
    (SND (EL (SUC i) t.contexts)).toDelete =
      (SND (EL i s.contexts)).toDelete) ⇒
  ^deletion_saved_absent n a t
Proof
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  Cases_on `i` >- gvs[EL] >>
  rename1 `SUC j < _` >>
  `j < LENGTH s.contexts ∧
   j < (if n = 1 then LENGTH s.contexts - 1
        else LENGTH s.contexts - n + 1)` by
    (Cases_on `n = 1` >> gvs[] >> decide_tac) >>
  metis_tac[]
QED

Theorem deletion_saved_absent_pop:
  0 < n ∧ n ≤ LENGTH t.contexts ∧
  LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
  ^deletion_saved_absent n a s ∧
  (∀i. i < LENGTH t.contexts ⇒
    (SND (EL i t.contexts)).toDelete =
      (SND (EL (SUC i) s.contexts)).toDelete) ⇒
  ^deletion_saved_absent n a t
Proof
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  `i < LENGTH t.contexts ∧
   SUC i < (if n = 1 then LENGTH s.contexts - 1
            else LENGTH s.contexts - n + 1)` by
    (Cases_on `n = 1` >> gvs[] >> decide_tac) >>
  metis_tac[]
QED

Theorem deletion_saved_protected_push:
  0 < n ∧ n ≤ LENGTH s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  ^deletion_saved_protected n a s ∧
  ((lookup_account a (SND (HD t.contexts)).accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a (SND (HD t.contexts)).accounts).code) ∧
  (∀i. i < LENGTH s.contexts ⇒
    lookup_account a (SND (EL (SUC i) t.contexts)).accounts =
      lookup_account a (SND (EL i s.contexts)).accounts) ⇒
  ^deletion_saved_protected n a t
Proof
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  Cases_on `i` >- gvs[EL] >>
  rename1 `SUC j < _` >>
  `j < LENGTH s.contexts ∧ j < LENGTH s.contexts - n` by decide_tac >>
  metis_tac[]
QED

Theorem deletion_saved_protected_pop:
  0 < n ∧ n ≤ LENGTH t.contexts ∧
  LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
  ^deletion_saved_protected n a s ∧
  (∀i. i < LENGTH t.contexts ⇒
    lookup_account a (SND (EL i t.contexts)).accounts =
      lookup_account a (SND (EL (SUC i) s.contexts)).accounts) ⇒
  ^deletion_saved_protected n a t
Proof
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  `i < LENGTH t.contexts ∧ SUC i < LENGTH s.contexts - n` by decide_tac >>
  metis_tac[]
QED

Theorem deletion_saved_absent_same_depth:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ LENGTH t.contexts = LENGTH s.contexts ∧
  ^deletion_saved_absent n a s ∧
  (∀i. i < LENGTH s.contexts ⇒
    (SND (EL i t.contexts)).toDelete = (SND (EL i s.contexts)).toDelete) ⇒
  ^deletion_saved_absent n a t
Proof
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  `i < LENGTH s.contexts` by (Cases_on `n = 1` >> gvs[] >> decide_tac) >>
  metis_tac[]
QED

Theorem deletion_saved_protected_same_depth:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ LENGTH t.contexts = LENGTH s.contexts ∧
  ^deletion_saved_protected n a s ∧
  (∀i. i < LENGTH s.contexts ⇒
    lookup_account a (SND (EL i t.contexts)).accounts =
      lookup_account a (SND (EL i s.contexts)).accounts) ⇒
  ^deletion_saved_protected n a t
Proof
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  `i < LENGTH s.contexts` by decide_tac >> metis_tac[]
QED

Theorem deletion_creation_certificate_push:
  0 < n ∧ n ≤ LENGTH s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  ^deletion_creation_certificate n a s ∧
  (lookup_account a s.rollback.accounts).nonce ≤
    (lookup_account a t.rollback.accounts).nonce ∧
  (lookup_account a s.rollback.accounts).nonce ≤
    (lookup_account a (SND (HD t.contexts)).accounts).nonce ∧
  ((FST (HD t.contexts)).msgParams.outputTo = Code a ⇒
    0 < (lookup_account a t.rollback.accounts).nonce) ∧
  (∀i. i < LENGTH s.contexts ⇒
    lookup_account a (SND (EL (SUC i) t.contexts)).accounts =
      lookup_account a (SND (EL i s.contexts)).accounts) ∧
  (∀i. i < LENGTH s.contexts ⇒
    (FST (EL (SUC i) t.contexts)).msgParams.outputTo =
      (FST (EL i s.contexts)).msgParams.outputTo) ⇒
  ^deletion_creation_certificate n a t
Proof
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  Cases_on `i` >- gvs[EL] >> rename1 `SUC k < _` >>
  `k < LENGTH s.contexts ∧ k < LENGTH s.contexts - n` by decide_tac >>
  `(FST (EL k s.contexts)).msgParams.outputTo = Code a` by metis_tac[] >>
  `0 < (lookup_account a s.rollback.accounts).nonce ∧
   ∀j. j < k ⇒ 0 < (lookup_account a (SND (EL j s.contexts)).accounts).nonce`
    by metis_tac[] >>
  conj_tac >- decide_tac >> gen_tac >> strip_tac >>
  Cases_on `j` >- (simp[EL] >> decide_tac) >>
  rename1 `SUC j < SUC k` >>
  `j < k ∧ j < LENGTH s.contexts` by decide_tac >> metis_tac[]
QED

Theorem deletion_creation_certificate_pop:
  0 < n ∧ n ≤ LENGTH t.contexts ∧
  LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
  ^deletion_creation_certificate n a s ∧
  (0 < (lookup_account a s.rollback.accounts).nonce ∧
   0 < (lookup_account a (SND (HD s.contexts)).accounts).nonce ⇒
     0 < (lookup_account a t.rollback.accounts).nonce) ∧
  (∀i. i < LENGTH t.contexts ⇒
    lookup_account a (SND (EL i t.contexts)).accounts =
      lookup_account a (SND (EL (SUC i) s.contexts)).accounts) ∧
  (∀i. i < LENGTH t.contexts ⇒
    (FST (EL i t.contexts)).msgParams.outputTo =
      (FST (EL (SUC i) s.contexts)).msgParams.outputTo) ⇒
  ^deletion_creation_certificate n a t
Proof
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  `i < LENGTH t.contexts ∧ SUC i < LENGTH s.contexts - n` by decide_tac >>
  `(FST (EL (SUC i) s.contexts)).msgParams.outputTo = Code a` by metis_tac[] >>
  `0 < (lookup_account a s.rollback.accounts).nonce ∧
   ∀j. j < SUC i ⇒
     0 < (lookup_account a (SND (EL j s.contexts)).accounts).nonce`
    by metis_tac[] >>
  conj_tac
  >- (`0 < (lookup_account a (SND (HD s.contexts)).accounts).nonce`
        by (first_x_assum (qspec_then `0` mp_tac) >> simp[EL]) >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  `j < LENGTH t.contexts ∧ SUC j < SUC i` by decide_tac >> metis_tac[]
QED

Theorem deletion_creation_certificate_same_depth:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ LENGTH t.contexts = LENGTH s.contexts ∧
  ^deletion_creation_certificate n a s ∧
  (lookup_account a s.rollback.accounts).nonce ≤
    (lookup_account a t.rollback.accounts).nonce ∧
  (∀i. i < LENGTH s.contexts ⇒
    lookup_account a (SND (EL i t.contexts)).accounts =
      lookup_account a (SND (EL i s.contexts)).accounts) ∧
  (∀i. i < LENGTH s.contexts ⇒
    (FST (EL i t.contexts)).msgParams.outputTo =
      (FST (EL i s.contexts)).msgParams.outputTo) ⇒
  ^deletion_creation_certificate n a t
Proof
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  `i < LENGTH s.contexts` by decide_tac >>
  `(FST (EL i s.contexts)).msgParams.outputTo = Code a` by metis_tac[] >>
  `0 < (lookup_account a s.rollback.accounts).nonce ∧
   ∀j. j < i ⇒ 0 < (lookup_account a (SND (EL j s.contexts)).accounts).nonce`
    by metis_tac[] >>
  conj_tac >- decide_tac >> gen_tac >> strip_tac >>
  `j < LENGTH s.contexts` by decide_tac >> metis_tac[]
QED

Theorem step_create_protected_original:
  s.contexts ≠ [] ∧ step_create two s = (r,t) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  lookup_account a t.originalAccounts =
    lookup_account a s.originalAccounts
Proof
  strip_tac >> drule_all step_create_deletion_projections >>
  simp[] >> strip_tac >> gvs[] >>
  `a ≠ b` by (strip_tac >> gvs[]) >>
  simp[lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM]
QED

val deletion_opcode = ``λa (s:execution_state) (t:execution_state).
  t.contexts ≠ [] ∧
  lookup_account a t.originalAccounts =
    lookup_account a s.originalAccounts ∧
  ¬MEM a t.rollback.toDelete ∧
  (MAP (λp. (SND p).toDelete) t.contexts =
     MAP (λp. (SND p).toDelete) s.contexts ∨
   MAP (λp. (SND p).toDelete) t.contexts =
     s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts)``;

Theorem step_inst_deletion_opcode:
  s.contexts ≠ [] ∧ step_inst op s = (r,t) ∧
  ¬MEM a s.rollback.toDelete ∧
  ¬account_empty (lookup_account a s.originalAccounts) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  ^deletion_opcode a s t
Proof
  strip_tac >> (
  Cases_on `op = SelfDestruct`
  >- (gvs[step_inst_def] >>
      drule (SRULE [preserves_when_def] step_self_destruct_deletion_rel) >>
      simp[] >> disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  Cases_on `op = Create ∨ op = Create2`
  >- (gvs[step_inst_def] >>
      `lookup_account a t.originalAccounts =
        lookup_account a s.originalAccounts`
        by metis_tac[step_create_protected_original] >>
      drule_all step_create_deletion_projections >> simp[] >>
      strip_tac >> gvs[]) >>
  Cases_on `op = Call ∨ op = CallCode ∨ op = DelegateCall ∨ op = StaticCall`
  >- (gvs[step_inst_def] >>
      drule (SRULE [preserves_when_def] step_call_deletion_call) >>
      simp[] >> disch_then drule >> simp[]) >>
  `preserves_when (λs. s.contexts ≠ []) ^deletion_exact (step_inst op)`
    by (irule step_inst_deletion_exact >> gvs[]) >>
  qpat_x_assum `preserves_when _ _ _` mp_tac >>
  simp[preserves_when_def] >> disch_then drule >>
  disch_then drule >> simp[])
QED

Theorem deletion_opcode_exact_trans:
  ^deletion_opcode a s t ∧ ^deletion_exact t u ⇒
  ^deletion_opcode a s u
Proof
  simp[] >> metis_tac[]
QED

Theorem step_inst_inc_pc_deletion_opcode:
  s.contexts ≠ [] ∧
  ignore_bind (step_inst op) (inc_pc_or_jump op) s = (r,t) ∧
  ¬MEM a s.rollback.toDelete ∧
  ¬account_empty (lookup_account a s.originalAccounts) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  ^deletion_opcode a s t
Proof
  strip_tac >> (
  Cases_on `step_inst op s` >> rename1 `step_inst op s = (q,u)` >>
  `^deletion_opcode a s u` by (irule step_inst_deletion_opcode >> metis_tac[]) >>
  Cases_on `q`
  >- (rename1 `step_inst op s = (INL x,u)` >> Cases_on `x` >>
      `inc_pc_or_jump op u = (r,t)` by
        gvs[ignore_bind_def, bind_def] >>
      `u.contexts ≠ []` by gvs[] >>
      drule_all (SRULE [preserves_when_def] inc_pc_or_jump_deletion_exact) >>
      strip_tac >> irule deletion_opcode_exact_trans >> metis_tac[]) >>
  gvs[ignore_bind_def, bind_def])
QED

val deletion_step_inner = ``do
  context <- get_current_context;
  case FLOOKUP context.msgParams.parsed context.pc of
  | SOME op => ignore_bind (step_inst op) (inc_pc_or_jump op)
  | NONE => if LENGTH context.msgParams.code ≤ context.pc
            then step_inst Stop else step_inst Invalid
  od``;

Theorem step_inner_deletion_opcode:
  s.contexts ≠ [] ∧ ^deletion_step_inner s = (r,t) ∧
  ¬MEM a s.rollback.toDelete ∧
  ¬account_empty (lookup_account a s.originalAccounts) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  ^deletion_opcode a s t
Proof
  strip_tac >> (
  qpat_x_assum `bind _ _ s = _` mp_tac >>
  simp[bind_def, get_current_context_def, return_def] >>
  Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
    (FST (HD s.contexts)).pc` >> simp[]
  >- (IF_CASES_TAC >> strip_tac >>
      irule (SRULE [] step_inst_deletion_opcode) >> metis_tac[]) >>
  strip_tac >> irule (SRULE [] step_inst_inc_pc_deletion_opcode) >> metis_tac[])
QED

Theorem deletion_saved_head_absent:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ 2 ≤ LENGTH s.contexts ∧
  ^deletion_saved_absent n a s ⇒
  ¬MEM a (SND (HD s.contexts)).toDelete
Proof
  simp[] >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >>
  Cases_on `n = 1` >> simp[EL]
QED

Theorem deletion_opcode_saved_head_absent:
  0 < n ∧ n ≤ LENGTH s.contexts ∧
  ^deletion_saved_absent n a s ∧ ¬MEM a s.rollback.toDelete ∧
  ^deletion_opcode a s t ∧ 2 ≤ LENGTH t.contexts ⇒
  ¬MEM a (SND (HD t.contexts)).toDelete
Proof
  simp[] >> rpt strip_tac
  >- (`LENGTH t.contexts = LENGTH s.contexts` by
        metis_tac[LENGTH_MAP] >>
      `¬MEM a (SND (HD s.contexts)).toDelete` by
        (irule deletion_saved_head_absent >> simp[] >> qexists_tac `n` >> simp[]) >>
      qpat_x_assum `MAP _ t.contexts = _` (mp_tac o Q.AP_TERM `HD`) >>
      Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `MAP _ t.contexts = _` mp_tac >>
  Cases_on `t.contexts` >> gvs[] >> metis_tac[]
QED

Theorem step_deletion_absent:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  ¬account_empty original ∧ step s = (r,t) ⇒
  ¬MEM a t.rollback.toDelete
Proof
  strip_tac >> (
  `s.contexts ≠ []` by gvs[wf_state_def] >>
  qpat_x_assum `step s = _` mp_tac >>
  rewrite_tac[step_def, handle_def] >>
  Cases_on `^deletion_step_inner s` >>
  rename1 `^deletion_step_inner s = (q,u)` >>
  `^deletion_opcode a s u` by
    (irule step_inner_deletion_opcode >> gvs[]) >>
  Cases_on `q` >> simp[]
  >- (strip_tac >> gvs[]) >>
  strip_tac >>
  `u.contexts ≠ []` by gvs[] >>
  `(2 ≤ LENGTH u.contexts ⇒ ¬MEM a (SND (HD u.contexts)).toDelete)` by
    (strip_tac >> irule deletion_opcode_saved_head_absent >> simp[] >>
     qexistsl_tac [`n`, `s`] >> gvs[]) >>
  drule_all handle_step_deletion_projections >> strip_tac >> gvs[])
QED

Theorem step_protected_original:
  s.contexts ≠ [] ∧ step s = (r,t) ∧
  ¬MEM a s.rollback.toDelete ∧
  ¬account_empty (lookup_account a s.originalAccounts) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  lookup_account a t.originalAccounts =
    lookup_account a s.originalAccounts
Proof
  strip_tac >> (
  qpat_x_assum `step s = _` mp_tac >>
  rewrite_tac[step_def, handle_def] >>
  Cases_on `^deletion_step_inner s` >>
  rename1 `^deletion_step_inner s = (q,u)` >>
  `^deletion_opcode a s u` by
    (irule step_inner_deletion_opcode >> gvs[]) >>
  Cases_on `q` >> simp[]
  >- (strip_tac >> gvs[]) >>
  strip_tac >> `u.contexts ≠ []` by gvs[] >>
  drule_all handle_step_deletion_projections >> strip_tac >> gvs[])
QED



Theorem handle_step_nonce_sources:
  s.contexts ≠ [] ∧ handle_step e s = (r,t) ⇒
  (lookup_account a t.rollback.accounts).nonce =
    (lookup_account a s.rollback.accounts).nonce ∨
  (2 ≤ LENGTH s.contexts ∧
   (lookup_account a t.rollback.accounts).nonce =
     (lookup_account a (SND (HD s.contexts)).accounts).nonce)
Proof
  strip_tac >> qhdtm_x_assum `handle_step` mp_tac >>
  simp[handle_step_def] >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[]) >>
  simp[handle_def] >>
  strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR) >>
  simp[] >> strip_tac >>
  drule_all handle_create_preserves_tl_and_snd_hd >> strip_tac >>
  drule_all handle_create_preserves_length >> strip_tac >>
  drule_all handle_create_nonce >>
  disch_then (qspec_then `a` assume_tac) >>
  drule_all handle_exception_rollback_sources >> strip_tac >> gvs[]
QED




Theorem step_deletion_continuing_protected:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  step s = (INL x,t) ∧ n ≤ LENGTH t.contexts ⇒
  (lookup_account a t.rollback.accounts).nonce ≠ 0 ∨
  ¬NULL (lookup_account a t.rollback.accounts).code
Proof
  simp[] >> strip_tac >> (
  `s.contexts ≠ []` by gvs[wf_state_def] >>
  qhdtm_x_assum `step` mp_tac >>
  simp[step_def, handle_def] >>
  Cases_on `^deletion_step_inner s` >>
  rename1 `^deletion_step_inner s = (q,u)` >>
  `^nonce_code_rel a s u` by
    (irule step_inner_nonce_code >> metis_tac[]) >>
  `same_frame_or_grow ^deletion_step_inner` by simp[] >>
  `LENGTH s.contexts ≤ LENGTH u.contexts` by
    (drule_all same_frame_or_grow_length >> simp[]) >>
  `u.contexts ≠ []` by (strip_tac >> gvs[]) >>
  `((lookup_account a u.rollback.accounts).nonce ≠ 0 ∨
    ¬NULL (lookup_account a u.rollback.accounts).code)` by
    (gvs[] >> decide_tac) >> (
  Cases_on `q` >> simp[] >> strip_tac
  >- gvs[] >>
  rename1 `handle_step e u = (INL (),t)` >>
  Cases_on `LENGTH u.contexts = LENGTH s.contexts`
  >- (drule_all handle_step_inl_pops >> strip_tac >>
      `n < LENGTH s.contexts` by decide_tac >>
      `same_frame_rel s u` by
        (drule_all same_frame_or_grow_eq_length >> simp[]) >>
      `((lookup_account a (SND (HD s.contexts)).accounts).nonce ≠ 0 ∨
        ¬NULL (lookup_account a (SND (HD s.contexts)).accounts).code)` by
        (qpat_x_assum `∀i. i < LENGTH s.contexts - n ⇒ _`
           (qspec_then `0` mp_tac) >> simp[EL]) >> (
      `((FST (HD s.contexts)).msgParams.outputTo = Code a ⇒
        0 < (lookup_account a s.rollback.accounts).nonce)` by
        (qpat_x_assum `∀i. _ ∧ _ ⇒ _` (qspec_then `0` mp_tac) >>
         simp[EL]) >>
      `(lookup_account a t.rollback.accounts).nonce ≠ 0 ∨
        ¬NULL (lookup_account a t.rollback.accounts).code` suffices_by metis_tac[] >>
      irule handle_step_protected_account >>
      qexistsl_tac [`e`,`INL ()`,`u`] >>
      gvs[same_frame_rel_def] >> gvs[] >> rpt strip_tac >> gvs[] >> decide_tac)) >>
  `LENGTH s.contexts < LENGTH u.contexts` by decide_tac >>
  `((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
    ¬NULL (lookup_account a s.rollback.accounts).code)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`) step_inner_inr_grow_protected_head >>
  disch_then (qspec_then `a` mp_tac) >>
  simp[] >> strip_tac >>
  `(lookup_account a t.rollback.accounts).nonce ≠ 0 ∨
        ¬NULL (lookup_account a t.rollback.accounts).code` suffices_by metis_tac[] >>
      irule handle_step_protected_account >>
  qexistsl_tac [`e`,`INL ()`,`u`] >> simp[]))
QED

Theorem deletion_step_pop_projections:
  wf_state s ∧ step s = (r,t) ∧ LENGTH t.contexts < LENGTH s.contexts ⇒
  LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
  (∀i. i < LENGTH t.contexts ⇒
    SND (EL i t.contexts) = SND (EL (SUC i) s.contexts) ∧
    (FST (EL i t.contexts)).msgParams.outputTo =
      (FST (EL (SUC i) s.contexts)).msgParams.outputTo)
Proof
  strip_tac >>
  `s.contexts ≠ [] ∧ outputTo_consistent_stack s ∧
   EVERY (wf_context o FST) s.contexts` by gvs[wf_state_def] >>
  drule_all step_pop_structure >> strip_tac >> (
  conj_tac >- metis_tac[LENGTH] >> gen_tac >> strip_tac >>
  Cases_on `i` >> gvs[EL] >>
  qpat_x_assum `s.contexts = _` (fn th => once_rewrite_tac[th]) >>
  simp[EL])
QED

Theorem deletion_same_frame_saved_projections:
  same_frame_rel s t ∧ i < LENGTH s.contexts ⇒
  SND (EL i t.contexts) = SND (EL i s.contexts) ∧
  (FST (EL i t.contexts)).msgParams.outputTo =
    (FST (EL i s.contexts)).msgParams.outputTo
Proof
  simp[same_frame_rel_def] >> strip_tac >>
  Cases_on `i` >> simp[EL]
QED


Theorem step_deletion_continuing_saved_protected:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  ¬account_empty original ∧ step s = (INL x,t) ∧ n ≤ LENGTH t.contexts ⇒
  ^deletion_saved_protected n a t
Proof
  strip_tac >>
  `wf_state s ∧ s.contexts ≠ [] ∧ outputTo_consistent s ∧
   outputTo_consistent_stack s ∧ n ≤ LENGTH s.contexts ∧
   ^deletion_saved_protected n a s` by
    (gvs[] >> metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent]) >>
  Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (`LENGTH t.contexts = SUC (LENGTH s.contexts)` by
        (qspecl_then [`s`,`INL x`,`t`] mp_tac (cj 1 step_push_structure) >> simp[]) >>
      `∀i. i < LENGTH s.contexts ⇒
        lookup_account a (SND (EL (SUC i) t.contexts)).accounts =
        lookup_account a (SND (EL i s.contexts)).accounts` by
        (rpt strip_tac >> irule step_growth_old_snapshot_lookup >>
         gvs[] >> metis_tac[]) >>
      `((lookup_account a (SND (HD t.contexts)).accounts).nonce ≠ 0 ∨
        ¬NULL (lookup_account a (SND (HD t.contexts)).accounts).code)` by
        (drule_all step_growth_saved_head_nonce_code >>
         disch_then (qspec_then `a` mp_tac) >> gvs[] >>
         strip_tac >> gvs[] >> decide_tac) >>
      mp_tac (BETA_RULE deletion_saved_protected_push) >>
      (impl_tac >- fs[]) >> simp[]) >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`same_frame_rel s t` by (irule step_same_frame >> metis_tac[]) >>
      `∀i. i < LENGTH s.contexts ⇒
        lookup_account a (SND (EL i t.contexts)).accounts =
        lookup_account a (SND (EL i s.contexts)).accounts` by
        (rpt strip_tac >> drule_all deletion_same_frame_saved_projections >> simp[]) >>
      mp_tac (BETA_RULE deletion_saved_protected_same_depth) >>
      (impl_tac >- fs[]) >> simp[]) >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  drule_all deletion_step_pop_projections >> strip_tac >>
  `∀i. i < LENGTH t.contexts ⇒
    lookup_account a (SND (EL i t.contexts)).accounts =
    lookup_account a (SND (EL (SUC i) s.contexts)).accounts` by metis_tac[] >>
  mp_tac (BETA_RULE deletion_saved_protected_pop) >>
  (impl_tac >- fs[]) >> simp[]
QED

Theorem step_deletion_continuing_saved_absent:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  ¬account_empty original ∧ step s = (INL x,t) ∧ n ≤ LENGTH t.contexts ⇒
  ^deletion_saved_absent n a t
Proof
  strip_tac >>
  `wf_state s ∧ s.contexts ≠ [] ∧ outputTo_consistent s ∧
   n ≤ LENGTH s.contexts ∧ ^deletion_saved_absent n a s ∧
   ¬MEM a s.rollback.toDelete` by
    (gvs[] >> metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent]) >>
  Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (`MAP (λp. (SND p).toDelete) t.contexts =
        s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts ∧
       LENGTH t.contexts = SUC (LENGTH s.contexts)` by
        (drule_all step_grow_dispatch >> strip_tac
         >- (drule_all step_call_deletion_projections >> strip_tac >> gvs[]) >>
         drule_all step_create_deletion_projections >> strip_tac >> gvs[]) >>
      `¬MEM a (SND (HD t.contexts)).toDelete` by
        (Cases_on `t.contexts` >> gvs[]) >>
      `∀i. i < LENGTH s.contexts ⇒
        (SND (EL (SUC i) t.contexts)).toDelete =
        (SND (EL i s.contexts)).toDelete` by
        (gen_tac >> strip_tac >>
         qpat_x_assum `MAP _ t.contexts = _` mp_tac >>
         once_rewrite_tac[LIST_EQ_REWRITE] >> strip_tac >>
         first_x_assum (qspec_then `SUC i` mp_tac) >>
         simp[EL_MAP, EL, GSYM MAP_TL]) >>
      mp_tac (BETA_RULE deletion_saved_absent_push) >>
      (impl_tac >- fs[]) >> simp[]) >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`same_frame_rel s t` by (irule step_same_frame >> metis_tac[]) >>
      `∀i. i < LENGTH s.contexts ⇒
        (SND (EL i t.contexts)).toDelete = (SND (EL i s.contexts)).toDelete` by
        (rpt strip_tac >> drule_all deletion_same_frame_saved_projections >> simp[]) >>
      mp_tac (BETA_RULE deletion_saved_absent_same_depth) >>
      (impl_tac >- fs[]) >> simp[]) >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  drule_all deletion_step_pop_projections >> strip_tac >>
  `∀i. i < LENGTH t.contexts ⇒
    (SND (EL i t.contexts)).toDelete =
    (SND (EL (SUC i) s.contexts)).toDelete` by metis_tac[] >>
  mp_tac (BETA_RULE deletion_saved_absent_pop) >>
  (impl_tac >- fs[]) >> simp[]
QED

Theorem step_growth_shifted_output:
  wf_state s ∧ step s = (r,t) ∧ LENGTH s.contexts < LENGTH t.contexts ∧
  i < LENGTH s.contexts ⇒
  (FST (EL (SUC i) t.contexts)).msgParams.outputTo =
  (FST (EL i s.contexts)).msgParams.outputTo
Proof
  strip_tac >>
  `s.contexts ≠ [] ∧ outputTo_consistent_stack s` by gvs[wf_state_def] >>
  `MAP FST (TL (TL t.contexts)) = MAP FST (TL s.contexts)` by
    (qspecl_then [`s`,`r`,`t`] mp_tac (cj 6 step_push_structure) >> simp[]) >>
  `(FST (EL 1 t.contexts)).msgParams = (FST (HD s.contexts)).msgParams` by
    (qspecl_then [`s`,`r`,`t`] mp_tac (cj 10 step_push_structure) >> simp[]) >>
  Cases_on `i`
  >- (qpat_x_assum `(FST (EL 1 _)).msgParams = _` mp_tac >>
      pure_once_rewrite_tac[ONE] >> simp[EL]) >>
  rename1 `SUC k < LENGTH s.contexts` >>
  qpat_x_assum `MAP FST _ = _` mp_tac >>
  once_rewrite_tac[LIST_EQ_REWRITE] >> strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >>
  simp[EL_MAP, EL, GSYM MAP_TL]
QED

Theorem step_pop_positive_nonce:
  wf_state s ∧ step s = (r,t) ∧ LENGTH t.contexts < LENGTH s.contexts ∧
  0 < (lookup_account a s.rollback.accounts).nonce ∧
  0 < (lookup_account a (SND (HD s.contexts)).accounts).nonce ⇒
  0 < (lookup_account a t.rollback.accounts).nonce
Proof
  strip_tac >>
  `s.contexts ≠ []` by gvs[wf_state_def] >>
  qhdtm_x_assum `step` mp_tac >> simp[step_def, handle_def] >>
  Cases_on `^deletion_step_inner s` >>
  rename1 `^deletion_step_inner s = (q,u)` >>
  `^nonce_code_rel a s u` by
    (irule step_inner_nonce_code >> metis_tac[]) >>
  `same_frame_or_grow ^deletion_step_inner` by simp[] >>
  `LENGTH s.contexts ≤ LENGTH u.contexts` by
    (drule_all same_frame_or_grow_length >> simp[]) >>
  `u.contexts ≠ []` by (strip_tac >> gvs[]) >>
  Cases_on `q` >> simp[] >> strip_tac
  >- gvs[] >>
  `LENGTH u.contexts = LENGTH s.contexts` by
    (drule_all handle_step_shrinks_by_one >> strip_tac >> decide_tac) >>
  `same_frame_rel s u` by
    (drule_all same_frame_or_grow_eq_length >> simp[]) >>
  drule_all handle_step_nonce_sources >>
  disch_then (qspec_then `a` mp_tac) >>
  gvs[same_frame_rel_def] >> strip_tac >> gvs[] >> decide_tac
QED

Theorem step_deletion_continuing_creation_certificate:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  ¬account_empty original ∧ step s = (INL x,t) ∧ n ≤ LENGTH t.contexts ⇒
  ^deletion_creation_certificate n a t
Proof
  strip_tac >>
  `wf_state s ∧ s.contexts ≠ [] ∧ outputTo_consistent_stack s ∧
   outputTo_consistent s ∧ n ≤ LENGTH s.contexts ∧
   ^deletion_creation_certificate n a s` by
    (gvs[] >> metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent]) >>
  Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (`LENGTH t.contexts = SUC (LENGTH s.contexts)` by
        (qspecl_then [`s`,`INL x`,`t`] mp_tac (cj 1 step_push_structure) >> simp[]) >>
      `∀i. i < LENGTH s.contexts ⇒
        lookup_account a (SND (EL (SUC i) t.contexts)).accounts =
        lookup_account a (SND (EL i s.contexts)).accounts` by
        (rpt strip_tac >> irule step_growth_old_snapshot_lookup >>
         gvs[] >> metis_tac[]) >>
      `∀i. i < LENGTH s.contexts ⇒
        (FST (EL (SUC i) t.contexts)).msgParams.outputTo =
        (FST (EL i s.contexts)).msgParams.outputTo` by
        (rpt strip_tac >> irule step_growth_shifted_output >> metis_tac[]) >>
      `(lookup_account a s.rollback.accounts).nonce ≤
        (lookup_account a t.rollback.accounts).nonce` by
        (drule_all step_growth_nonce_code >>
         disch_then (qspec_then `a` mp_tac) >> simp[]) >>
      `(lookup_account a s.rollback.accounts).nonce ≤
        (lookup_account a (SND (HD t.contexts)).accounts).nonce` by
        (drule_all step_growth_saved_head_nonce_code >>
         disch_then (qspec_then `a` mp_tac) >> simp[]) >>
      `((FST (HD t.contexts)).msgParams.outputTo = Code a ⇒
        0 < (lookup_account a t.rollback.accounts).nonce)` by
        (strip_tac >> irule step_growth_nonce_certificate >> metis_tac[]) >>
      mp_tac (BETA_RULE deletion_creation_certificate_push) >>
      (impl_tac >- (fs[] >> metis_tac[])) >> simp[]) >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`same_frame_rel s t` by (irule step_same_frame >> metis_tac[]) >>
      `∀i. i < LENGTH s.contexts ⇒
        SND (EL i t.contexts) = SND (EL i s.contexts) ∧
        (FST (EL i t.contexts)).msgParams.outputTo =
        (FST (EL i s.contexts)).msgParams.outputTo` by
        (gen_tac >> strip_tac >> drule_all deletion_same_frame_saved_projections >> simp[]) >>
      `(lookup_account a s.rollback.accounts).nonce ≤
        (lookup_account a t.rollback.accounts).nonce` by
        (drule_all same_frame_nonce_monotone >> simp[]) >>
      mp_tac (BETA_RULE deletion_creation_certificate_same_depth) >>
      (impl_tac >- (fs[] >> metis_tac[])) >> simp[]) >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  `0 < (lookup_account a s.rollback.accounts).nonce ∧
   0 < (lookup_account a (SND (HD s.contexts)).accounts).nonce ⇒
   0 < (lookup_account a t.rollback.accounts).nonce` by
    (strip_tac >> irule step_pop_positive_nonce >> metis_tac[]) >>
  drule_all deletion_step_pop_projections >> strip_tac >>
  mp_tac (BETA_RULE deletion_creation_certificate_pop) >>
  (impl_tac >- (fs[] >> metis_tac[])) >> simp[]
QED

Theorem step_deletion_continuing_inv:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  ¬account_empty original ∧ step s = (INL x,t) ∧ n ≤ LENGTH t.contexts ⇒
  ^deletion_run_inv n a original t
Proof
  strip_tac >>
  `^deletion_creation_certificate n a t` by
    (irule step_deletion_continuing_creation_certificate >> metis_tac[]) >>
  `^deletion_saved_absent n a t` by
    (irule step_deletion_continuing_saved_absent >> metis_tac[]) >>
  `^deletion_saved_protected n a t` by
    (irule step_deletion_continuing_saved_protected >> metis_tac[]) >>
  `(lookup_account a t.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a t.rollback.accounts).code` by
    (irule step_deletion_continuing_protected >> metis_tac[]) >>
  `¬MEM a t.rollback.toDelete` by
    (irule step_deletion_absent >> metis_tac[]) >>
  `lookup_account a t.originalAccounts = original` by
    (`lookup_account a t.originalAccounts = lookup_account a s.originalAccounts`
       by (irule step_protected_original >> gvs[] >> metis_tac[wf_state_def]) >>
     gvs[]) >>
  `wf_state t` by
    (`wf_state s` by gvs[] >> drule step_preserves_wf_state >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Theorem run_call_to_delete:
  wf_state es ∧
  run_call es = SOME (r, es') ∧
  MEM a es'.rollback.toDelete ⇒
  MEM a es.rollback.toDelete ∨
  (2 ≤ LENGTH es.contexts ∧ MEM a (SND (HD es.contexts)).toDelete) ∨
  account_empty (lookup_account a es.originalAccounts) ∨
  (lookup_account a es.rollback.accounts).nonce = 0 ∧
  NULL (lookup_account a es.rollback.accounts).code
Proof
  strip_tac >> spose_not_then strip_assume_tac >>
  `0 < LENGTH es.contexts` by
    (Cases_on `es.contexts` >> gvs[wf_state_def]) >>
  `^deletion_run_inv (LENGTH es.contexts) a
    (lookup_account a es.originalAccounts) es` by
    (irule deletion_run_inv_initial >> simp[] >> metis_tac[]) >>
  gvs[run_call_def] >>
  `(λp. ¬MEM a (SND p).rollback.toDelete ∧
    ((ISL (FST p) ∧ LENGTH es.contexts ≤ LENGTH (SND p).contexts) ⇒
     ^deletion_run_inv (LENGTH es.contexts) a
       (lookup_account a es.originalAccounts) (SND p))) (r,es')`
    suffices_by simp[] >>
  irule (MP_CANON OWHILE_INV_IND) >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  simp[] >> rpt gen_tac >> pairarg_tac >> simp[] >>
  strip_tac >> Cases_on `step s''` >> simp[] >>
  `^deletion_run_inv (LENGTH es.contexts) a
     (lookup_account a es.originalAccounts) s''` by
    (qpat_x_assum `ISL _ ∧ _ ⇒ _` mp_tac >> simp[GREATER_EQ] >> strip_tac >> asm_rewrite_tac[]) >>
  conj_tac
  >- (irule step_deletion_absent >>
      qexistsl_tac [`LENGTH es.contexts`, `lookup_account a es.originalAccounts`,
                    `q`, `s''`] >> simp[]) >>
  strip_tac >> Cases_on `q` >> gvs[] >>
  `^deletion_run_inv (LENGTH es.contexts) a
     (lookup_account a es.originalAccounts) r'` by
    (irule step_deletion_continuing_inv >> simp[] >>
     qexists_tac `s''` >> simp[GREATER_EQ] >> asm_rewrite_tac[]) >>
  gvs[] >> asm_rewrite_tac[]
QED
