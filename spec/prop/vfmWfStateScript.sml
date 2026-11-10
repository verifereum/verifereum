(* ==========================================================================
 * A step preserves wf_state: pushing or popping a context keeps the
 * stack-room, gas-stack and outputTo invariants of the context stack.
 * ========================================================================== *)
Theory vfmWfState
Ancestors
  combin pair option pred_set list rich_list sum
  arithmetic finite_map While vfmTypes vfmConstants
  vfmContext vfmState vfmExecution vfmExecutionProp
  vfmStoragePredicates vfmSameFrame vfmStaticCalls
  vfmDecreasesGas vfmStepLength vfmHandleStep vfmRunWithinFrame
  vfmHeadStack vfmHeadGas vfmPreserves
Libs
  dep_rewrite BasicProvers

(* Per-context outputTo consistency, needed across pops. *)

(* EIP-8037: the account-creation charge and its credit, and the create that
   aborts before it enters a child.  Each wraps a state-gas meter action, so
   `vfmSameFrame`'s `preserves_same_frame_state_gas_meter` and
   `vfmStoragePredicates`' `preserves_rollback_state_gas_meter` cover the
   bodies; these are the wrappers, named here because the charge and the
   credit are what the call/create prefixes below peel. *)

Theorem preserves_same_frame_charge_new_account[simp]:
  preserves_same_frame (charge_new_account charged)
Proof
  Cases_on `charged` >> rw[charge_new_account_def]
QED

Theorem preserves_same_frame_credit_new_account[simp]:
  preserves_same_frame (credit_new_account charged)
Proof
  Cases_on `charged` >> rw[credit_new_account_def]
QED

Theorem preserves_storage_charge_new_account[simp]:
  preserves_storage (charge_new_account charged)
Proof
  Cases_on `charged` >> rw[charge_new_account_def]
QED

Theorem preserves_storage_credit_new_account[simp]:
  preserves_storage (credit_new_account charged)
Proof
  Cases_on `charged` >> rw[credit_new_account_def]
QED

Theorem preserves_same_frame_abort_create[simp]:
  preserves_same_frame abort_create
Proof
  rw[abort_create_def]
QED

(* The head-gas instance for the charge: `charge_state_gas` either moves only
   `stateGasLeft` or spills the excess through `consume_gas`, so the head
   frame's `gasUsed` never falls.  (The matching head-stack instance is
   vfmHeadStack's `preserves_head_stack_state_gas_meter`; the credit is not
   monotone in `gasUsed`, so it has no instance here.) *)

Theorem preserves_head_gas_mono_charge_state_gas[simp]:
  preserves_head_gas_mono (charge_state_gas n)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     charge_state_gas_def, bind_def, get_current_context_def, return_def,
     fail_def, assert_def, set_current_context_def, ignore_bind_def,
     consume_gas_def, LET_THM]
  (* EIP-8037: unfolding the charge leaves its whole body in a hypothesis, a
     `case` whose branches are the two pool paths, so the frame the goal reads
     can only be reached by taking that hypothesis into the goal and splitting
     it there.  An empty stack fails before the body, which `Cases_on` settles
     with the charge's own guard in hand. *)
  >> Cases_on `s.contexts` >> gvs[]
  >> TRY (rpt (pop_assum mp_tac) >> rpt IF_CASES_TAC >> rpt disch_tac
          >> gvs[consume_gas_def, get_current_context_def,
                 set_current_context_def, charge_state_gas_def,
                 assert_def, bind_def, ignore_bind_def, return_def,
                 fail_def, LET_THM, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ, APPLY_UPDATE_THM]
          >> rw[] >> NO_TAC)
  >> rpt (gvs[AllCaseEqs()] >> decide_tac)
QED

Theorem preserves_head_gas_mono_charge_new_account[simp]:
  preserves_head_gas_mono (charge_new_account charged)
Proof
  Cases_on `charged` >> rw[charge_new_account_def]
QED

Theorem outputTo_consistent_stack_imp_consistent:
  outputTo_consistent_stack s ⇒ outputTo_consistent s
Proof
  rw[outputTo_consistent_stack_def, outputTo_consistent_def]
  >> Cases_on `s.contexts` >> gvs[outputTo_consistent_ctx_def]
QED

(* Single-step preservation of run_call_inv: split on same-frame/push/pop. *)


(* Same-frame step storage preservation outside final storageKeys. *)

(* Same-frame case: non-callee storage is unchanged by callee_local_changes;
 * callee storage can change only via SSTORE, which first access-lists the slot. *)



(* Pushed rollback storage: when CALL/CREATE pushes, the new head's saved
 * rollback has the old rollback's storage. *)

(* proceed_call captures s.rollback as the pushed rollback. *)
Theorem proceed_call_push_structure:
  proceed_call op sender address value argsOffset argsSize code stipend
               outputTo s = (r, s') ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1 ∧
  TL (TL s'.contexts) = TL s.contexts ∧
  FST (HD (TL s'.contexts)) =
    (FST (HD s.contexts) with stateGasLeft := 0) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  (FST (HD s'.contexts)).msgParams.outputTo = outputTo ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h`
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def, drain_state_gas_reservoir_def,
          bind_def, ignore_bind_def, get_current_context_def,
          set_current_context_def, return_def, get_rollback_def,
          read_memory_def, get_caller_def, get_value_def, get_static_def,
          get_accounts_def]
  >> Cases_on `op <> CallCode /\ 0 < value`
  >> (simp[update_accounts_def, return_def]
  >> simp[push_context_def, return_def, bind_def]
  >> qmatch_goalsub_abbrev_tac `(if _ then _ else _) ss`
  >> Cases_on `fIN address precompile_addresses`
  >- (simp[] >> strip_tac
      >> `ss.contexts <> []` by simp[Abbr`ss`]
      >> qmatch_asmsub_abbrev_tac `dpa ss = (_, _)`
      >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
      >> pop_assum mp_tac
      >> rewrite_tac[preserves_same_frame_def]
      >> disch_then drule >> simp[]
      >> simp[same_frame_rel_def, Abbr`ss`]
      >> strip_tac >> gvs[initial_context_def, initial_msg_params_def])
  >> simp[return_def, Abbr`ss`, initial_context_def, initial_msg_params_def]
  >> strip_tac >> gvs[])
QED

Theorem proceed_call_saved_parent_rollback:
  proceed_call op sender address value argsOffset argsSize code stipend
               outputTo s = (r, s') ∧ s.contexts ≠ [] ⇒
  SND (HD (TL s'.contexts)) = SND (HD s.contexts)
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h`
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def, drain_state_gas_reservoir_def,
          bind_def, ignore_bind_def, get_current_context_def,
          set_current_context_def, return_def, get_rollback_def,
          read_memory_def, get_caller_def, get_value_def, get_static_def,
          get_accounts_def]
  >> Cases_on `op <> CallCode /\ 0 < value`
  >> (simp[update_accounts_def, return_def, push_context_def, bind_def]
      >> qmatch_goalsub_abbrev_tac `(if _ then _ else _) ss`
      >> Cases_on `fIN address precompile_addresses`
      >- (simp[] >> strip_tac
          >> `ss.contexts <> []` by simp[Abbr`ss`]
          >> qmatch_asmsub_abbrev_tac `dpa ss = (_, _)`
          >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
          >> pop_assum mp_tac
          >> rewrite_tac[preserves_same_frame_def]
          >> disch_then drule >> simp[]
          >> simp[same_frame_rel_def, Abbr`ss`]
          >> strip_tac >> gvs[])
      >> simp[return_def, Abbr`ss`] >> strip_tac >> gvs[])
QED

Theorem proceed_create_push_structure:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1 ∧
  TL (TL s'.contexts) = TL s.contexts ∧
  FST (HD (TL s'.contexts)) =
    (FST (HD s.contexts) with stateGasLeft := 0) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def, drain_state_gas_reservoir_def,
          get_current_context_def, set_current_context_def,
          bind_def, ignore_bind_def, return_def, get_accounts_def]
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  >> strip_tac
  >> drule push_context_effect >> strip_tac >> gvs[]
  >> simp[outputTo_consistent_ctx_def, initial_context_def,
          initial_msg_params_def]
  >> simp[set_last_accounts_def, MAP_SNOC, MAP_FRONT]
  >> Cases_on `s.contexts` >> gvs[SUBSET_DEF]
QED

Theorem proceed_create_saved_parent_rollback:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ⇒
  SND (HD (TL s'.contexts)) = SND (HD s.contexts)
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def, drain_state_gas_reservoir_def,
          get_current_context_def, set_current_context_def,
          bind_def, ignore_bind_def, return_def, update_accounts_def,
          get_rollback_def, get_original_def, set_original_def, fail_def,
          push_context_def, get_accounts_def]
  >> strip_tac >> gvs[]
QED

Theorem proceed_call_pushed_rb_storage:
  proceed_call op sender address value argsOffset argsSize code stipend
                outputTo s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
      (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h`
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def, drain_state_gas_reservoir_def,
          bind_def, ignore_bind_def, get_current_context_def,
          set_current_context_def, return_def, get_rollback_def,
          read_memory_def, get_caller_def, get_value_def, get_static_def,
          get_accounts_def]
  >> Cases_on `op <> CallCode /\ 0 < value`
  >> (simp[update_accounts_def, return_def, push_context_def, bind_def]
      >> qmatch_goalsub_abbrev_tac `(if _ then _ else _) ss`
      >> Cases_on `fIN address precompile_addresses`
      >- (simp[] >> strip_tac
          >> `ss.contexts <> []` by simp[Abbr`ss`]
          >> qmatch_asmsub_abbrev_tac `dpa ss = (_, _)`
          >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
          >> pop_assum mp_tac
          >> rewrite_tac[preserves_same_frame_def]
          >> disch_then drule >> simp[]
          >> simp[same_frame_rel_def, Abbr`ss`]
          >> strip_tac >> gvs[])
      >> simp[return_def, Abbr`ss`] >> strip_tac >> gvs[])
QED

(* Intermediate: proceed_create captures s.rollback (post increment_nonce)
   as the pushed rollback. increment_nonce and set_original do not touch
   s.rollback.accounts.storage. transfer_value happens AFTER get_rollback,
   so it doesn't affect the captured rollback. *)
Theorem proceed_create_pushed_rb_storage:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
      (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def, drain_state_gas_reservoir_def,
          get_current_context_def, set_current_context_def,
          bind_def, ignore_bind_def, return_def, get_accounts_def]
  (* update_accounts (increment_nonce senderAddress) *)
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  (* get_rollback: captures increment_nonce'd rollback. *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  (* get_original / set_original: don't modify s.rollback. *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  (* update_accounts (transfer_value o increment_nonce): modifies s.rollback,
     but the captured `rollback` variable already holds the pre-transfer one. *)
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  (* push_context. *)
  >> strip_tac
  >> drule push_context_effect >> strip_tac >> gvs[]
  (* After push: HD s'.contexts = (ctx, rollback-with-incremented-nonce).
     increment_nonce preserves storage at every address. *)
  >> rw[lookup_account_def, increment_nonce_def,
        combinTheory.APPLY_UPDATE_THM, finite_mapTheory.FLOOKUP_UPDATE]
  >> gvs[update_account_def, APPLY_UPDATE_THM]
  >> rw[]
QED

(* proceed_call push structure.

   EIP-8037: the call drains the calling frame's reservoir before it
   pushes.  `drain_state_gas_reservoir` (`spec/vfmExecutionScript.sml:653`)
   sets the current context's `stateGasLeft := 0` and returns the old
   value, `proceed_call_def` (`:1798`) opens with it and builds the new
   frame from that return (`:1822`), and `push_context` (`:270`) is
   `contexts updated_by CONS crb`.  So the output's tail is the parent
   *with its reservoir zeroed*, and the tail equality holds only of the
   frames below the parent; the parent's one moved field is named here.
   Checked witness for the old form (since removed with the other
   probes): a return whose parent frame has had its reservoir zeroed
   while the frames below it are unchanged. *)

(* CALL/CREATE wrappers: same-frame storage-preserving prefixes, then proceed_*. *)

(* Composable predicate: if m grows, the pushed rollback preserves storage. *)
Definition preserves_pushed_rb_storage_def:
  preserves_pushed_rb_storage (m : α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ∧
             LENGTH s'.contexts > LENGTH s.contexts ⇒
      ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
          (lookup_account a s.rollback.accounts).storage
End

(* Same-frame prefixes cannot grow, so the pushed-rb property is vacuous. *)
Theorem preserves_pushed_rb_storage_of_same_frame[simp]:
  preserves_same_frame m ⇒ preserves_pushed_rb_storage m
Proof
  rw[preserves_same_frame_def, preserves_pushed_rb_storage_def]
  >> first_x_assum drule >> simp[same_frame_rel_def]
QED

(* bind composition for pushed-rb storage. *)
Theorem preserves_pushed_rb_storage_bind:
  preserves_storage g ∧ preserves_same_frame g ∧
  (∀x. preserves_pushed_rb_storage (f x)) ⇒
  preserves_pushed_rb_storage (bind g f)
Proof
  rw[preserves_pushed_rb_storage_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> fs[preserves_storage_def, preserves_same_frame_def]
  >> rpt (first_x_assum drule) >> simp[same_frame_rel_def] >> strip_tac
  >> rpt strip_tac
  (* s_mid has same contexts and storage as s. *)
  >> qmatch_asmsub_rename_tac `g s = (_, s_mid)`
  >> `s_mid.contexts ≠ []` by (Cases_on `s.contexts` >> Cases_on `s_mid.contexts` >> fs[])
  >> `LENGTH s'.contexts > LENGTH s_mid.contexts` by fs[]
  >> first_x_assum drule >> simp[]
  >> disch_then (qspec_then `a` mp_tac) >> simp[]
  >> gvs[lookup_storage_def, FUN_EQ_THM]
QED

Theorem preserves_pushed_rb_storage_ignore_bind:
  preserves_storage g ∧ preserves_same_frame g ∧
  preserves_pushed_rb_storage f ⇒
  preserves_pushed_rb_storage (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule preserves_pushed_rb_storage_bind >> rw[]
QED

Theorem preserves_pushed_rb_storage_cond[simp]:
  preserves_pushed_rb_storage m1 ∧ preserves_pushed_rb_storage m2 ⇒
  preserves_pushed_rb_storage (if b then m1 else m2)
Proof
  rw[]
QED

(* Base case: proceed_call preserves pushed rb storage. *)
Theorem preserves_pushed_rb_storage_proceed_call[simp]:
  preserves_pushed_rb_storage
    (proceed_call op sender address value argsOffset argsSize
                  code stipend outputTo)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all proceed_call_pushed_rb_storage
  >> simp[]
QED

Theorem preserves_pushed_rb_storage_proceed_create[simp]:
  preserves_pushed_rb_storage
    (proceed_create senderAddress address value code cappedGas)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all proceed_create_pushed_rb_storage
  >> simp[]
QED

(* Now step_call = a bunch of preserves_storage+preserves_same_frame
   primitives followed by either abort_call_value (which is
   preserves_same_frame, vacuously preserves_pushed_rb_storage),
   abort_unuse (likewise), or proceed_call. *)
Theorem preserves_pushed_rb_storage_step_call[simp]:
  preserves_pushed_rb_storage (step_call op)
Proof
  simp[step_call_def]
  (* Shape mirrors preserves_storage_step_call's proof. Every bind
     prefix is preserves_storage + preserves_same_frame; use the
     bind rule with those two side conditions. *)
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[]
  >> reverse conj_tac >- (CASE_TAC >> simp[])
  >> Cases >> simp[]
  (* EIP-8037: the opcode's execution gas, the creation charge in state
     gas, the static check and the memory expansion come before the
     child's grant is read. *)
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
QED

(* abort_create_exists doesn't grow contexts, so vacuously preserves
   pushed-rb storage. Unlike abort_call_value/abort_unuse, it is NOT
   unconditionally preserves_same_frame (it requires the sender address
   to match the current callee), so we prove it from the length lemma. *)
Theorem preserves_pushed_rb_storage_abort_create_exists[simp]:
  preserves_pushed_rb_storage (abort_create_exists a)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all abort_create_exists_length
  >> simp[]
QED

Theorem preserves_pushed_rb_storage_step_create[simp]:
  preserves_pushed_rb_storage (step_create two)
Proof
  simp[step_create_def]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> rpt (irule preserves_pushed_rb_storage_ignore_bind >> simp[])
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  (* EIP-8037: the destination's creation is charged in state gas before
     the child's grant is withheld, so a spill thins what is withheld. *)
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind
  >> simp[preserves_same_frame_state_gas_meter] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
QED

(* Final user-facing lemmas. *)
Theorem step_call_pushed_rb_storage:
  ∀op s r s'. step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
        (lookup_account a s.rollback.accounts).storage
Proof
  metis_tac[preserves_pushed_rb_storage_step_call,
            preserves_pushed_rb_storage_def]
QED

Theorem step_create_pushed_rb_storage:
  ∀two s r s'. step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
        (lookup_account a s.rollback.accounts).storage
Proof
  metis_tac[preserves_pushed_rb_storage_step_create,
            preserves_pushed_rb_storage_def]
QED

(* step_call growth structure: peel same-frame prefixes, then proceed_call. *)
Theorem step_call_push_structure:
  step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  TL (TL s'.contexts) = TL s.contexts ∧
  SND (HD (TL s'.contexts)) = SND (HD s.contexts) ∧
  (FST (HD (TL s'.contexts))).msgParams = (FST (HD s.contexts)).msgParams ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  simp[step_call_def] >> strip_tac
  (* Peel pop_stack *)
  >> qmatch_asmsub_abbrev_tac`pop_stack n`
  >> `preserves_same_frame (pop_stack n)` by simp[]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> pairarg_tac >> gvs[]
  >> `sm.contexts ≠ []` by (strip_tac >> gvs[same_frame_rel_def])
  >> `LENGTH sm.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
  (* Peel memory_expansion_info *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ sm = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sm s2`
  >> `same_frame_rel s s2` by metis_tac[same_frame_rel_trans]
  >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel consume_gas *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s2 s3`
  >> `same_frame_rel s s3` by metis_tac[same_frame_rel_trans]
  >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel expand_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s3 s4`
  >> `same_frame_rel s s4` by metis_tac[same_frame_rel_trans]
  >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s4 s5`
  >> `same_frame_rel s s5` by metis_tac[same_frame_rel_trans]
  >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> pairarg_tac >> gvs[ignore_bind_def]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s5 s6`
  >> `same_frame_rel s s6` by metis_tac[same_frame_rel_trans]
  >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* EIP-8037: the creation charge, the static check and the memory
     expansion come before the child's grant is read. *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s6 sc`
  >> `same_frame_rel s sc` by metis_tac[same_frame_rel_trans]
  >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sc s7`
  >> `same_frame_rel s s7` by metis_tac[same_frame_rel_trans]
  >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s7 s8`
  >> `same_frame_rel s s8` by metis_tac[same_frame_rel_trans]
  >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* The grant is computed after the charge, so the 63/64 rule sees the
     execution gas a spill thinned. *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s8 sd`
  >> `same_frame_rel s sd` by metis_tac[same_frame_rel_trans]
  >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> pairarg_tac >> gvs[ignore_bind_def]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sd s9`
  >> `same_frame_rel s s9` by metis_tac[same_frame_rel_trans]
  >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_callee *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s9 s0`
  >> `same_frame_rel s s0` by metis_tac[same_frame_rel_trans]
  >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
  >> gvs[Ntimes COND_RATOR 2]
  >> Cases_on`bbb` >> gs[]
  >- (
    drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
    >> simp[])
  (* Peel set_return_data via ignore_bind *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s0 sa`
  >> `same_frame_rel s sa` by metis_tac[same_frame_rel_trans]
  >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_num_contexts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sa sb`
  >> `same_frame_rel s sb` by metis_tac[same_frame_rel_trans]
  >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Now at the conditional: if value check then abort else continue *)
  (* Second conditional: if depth/code check then abort else proceed_call *)
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
  >> gvs[COND_RATOR]
  >> Cases_on`bbb` >> gs[]
  >- (
    drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
    >> simp[])
  (* Now we have proceed_call sm = (_, s') with growth, and same_frame_rel s sm *)
  >> drule_all_then assume_tac proceed_call_saved_parent_rollback
  >> drule_all proceed_call_push_structure
  >> strip_tac
  (* The prefix preserves the parent's saved rollback and msgParams. *)
  >> `TL sb.contexts = TL s.contexts` by ( fs[same_frame_rel_def] )
  >> gvs[]
  >> conj_asm1_tac >- gvs[same_frame_rel_def]
  >> conj_asm1_tac >- gvs[same_frame_rel_def]
  >> conj_tac >- metis_tac[SUBSET_TRANS, same_frame_rel_def]
  (* outputTo_consistent: outputTo = Memory from step_call, so Code a is vacuous *)
  >> conj_tac >- simp[outputTo_consistent_ctx_def]
  >> metis_tac[SUBSET_TRANS, same_frame_rel_def]
QED

(* step_create growth structure. set_original updates originalAccounts
 * and leaves saved rollback pairs unchanged. *)
Theorem step_create_push_structure:
  step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
  (∀i. i < LENGTH s.contexts ⇒
       (SND (EL i (TL s'.contexts))).accesses = (SND (EL i s.contexts)).accesses) ∧
  (FST (HD (TL s'.contexts))).msgParams = (FST (HD s.contexts)).msgParams ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys ∧
  (∀a. a ≠ (FST (HD s'.contexts)).msgParams.callee ⇒
     (lookup_account a (SND (HD (TL s'.contexts))).accounts).storage =
     (lookup_account a (SND (HD s.contexts)).accounts).storage) ∧
  (∀i. i < LENGTH s.contexts - 1 ⇒
     (SND (EL i (TL s'.contexts))).accounts =
     (SND (EL i s.contexts)).accounts) ∧
  (∀a. a ≠ (FST (HD s'.contexts)).msgParams.callee ⇒
    (lookup_account a (SND (EL (LENGTH s.contexts) s'.contexts)).accounts).storage =
    (lookup_account a (SND (LAST s.contexts)).accounts).storage)
Proof
  simp[step_create_def] >> strip_tac
  (* Peel pop_stack *)
  >> qmatch_asmsub_abbrev_tac`pop_stack n`
  >> `preserves_same_frame (pop_stack n)` by simp[]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> `sm.contexts ≠ []` by (strip_tac >> gvs[same_frame_rel_def])
  >> `LENGTH sm.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
  (* Peel memory_expansion_info *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ sm = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sm s2`
  >> `same_frame_rel s s2` by metis_tac[same_frame_rel_trans]
  >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel consume_gas *)
  >> gvs[ignore_bind_def]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s2 s3`
  >> `same_frame_rel s s3` by metis_tac[same_frame_rel_trans]
  >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel expand_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s3 s4`
  >> `same_frame_rel s s4` by metis_tac[same_frame_rel_trans]
  >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel read_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s4 s5`
  >> `same_frame_rel s s5` by metis_tac[same_frame_rel_trans]
  >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_callee *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s5 s6`
  >> `same_frame_rel s s6` by metis_tac[same_frame_rel_trans]
  >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_accounts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s6 s7`
  >> `same_frame_rel s s7` by metis_tac[same_frame_rel_trans]
  >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel assert (code length) via ignore_bind *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s7 s8`
  >> `same_frame_rel s s8` by metis_tac[same_frame_rel_trans]
  >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel assert_not_static *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s8 s0`
  >> `same_frame_rel s s0` by metis_tac[same_frame_rel_trans]
  >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel set_return_data *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s0 sa`
  >> `same_frame_rel s sa` by metis_tac[same_frame_rel_trans]
  >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_num_contexts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sa sb`
  >> `same_frame_rel s sb` by metis_tac[same_frame_rel_trans]
  >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Split the preliminary failure condition. *)
  >> qmatch_asmsub_abbrev_tac`COND preliminaryFailure _ _ _ = (_, _)`
  >> gvs[COND_RATOR]
  >> qpat_x_assum`COND preliminaryFailure _ _ = _`mp_tac
  >> IF_CASES_TAC
  >- ((* abort_create: preserves_same_frame, can't grow *)
      strip_tac >>
      drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
      >> simp[])
  >> strip_tac
  (* Peel access_address *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sb sd`
  >> `same_frame_rel s sd` by metis_tac[same_frame_rel_trans]
  >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel ensure_storage_in_domain *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sd sx`
  >> `same_frame_rel s sx` by metis_tac[same_frame_rel_trans]
  >> `sx.contexts ≠ [] ∧ LENGTH sx.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* EIP-8037: the destination's creation, charged before the child's
     grant is withheld so a spill thins what is withheld. *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sx sy`
  >> `same_frame_rel s sy` by metis_tac[same_frame_rel_trans]
  >> `sy.contexts ≠ [] ∧ LENGTH sy.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel withhold_create_gas *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[preserves_same_frame_state_gas_meter] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sy se`
  >> `same_frame_rel s se` by metis_tac[same_frame_rel_trans]
  >> `se.contexts ≠ [] ∧ LENGTH se.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Now at the collision conditional. *)
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
  >> gvs[COND_RATOR]
  >> qpat_x_assum`COND bbb _ _ = _`mp_tac
  >> IF_CASES_TAC
  >- ((* abort_create_exists: length_preserves, can't grow *)
      strip_tac >>
      drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists)
      >> simp[])
  (* Now we have proceed_create se = (_, s') with growth, and same_frame_rel s se *)
  >> strip_tac
  >> qpat_x_assum `s.contexts ≠ []` mp_tac
  >> qpat_x_assum `se.contexts ≠ []` mp_tac
  >> qpat_x_assum `same_frame_rel s se` mp_tac
  >> qpat_x_assum `proceed_create _ _ _ _ _ se = _` mp_tac
  >> POP_ASSUM_LIST (K all_tac)
  >> ntac 4 strip_tac
  >> drule_all_then assume_tac proceed_create_saved_parent_rollback
  >> drule_all proceed_create_push_structure >> strip_tac
  >> `TL se.contexts = TL s.contexts /\
      SND (HD se.contexts) = SND (HD s.contexts) /\
      (FST (HD se.contexts)).msgParams = (FST (HD s.contexts)).msgParams /\
      toSet s.rollback.accesses.storageKeys SUBSET toSet se.rollback.accesses.storageKeys`
     by fs[same_frame_rel_def]
  >> qpat_x_assum `same_frame_rel _ _` kall_tac
  >> qhdtm_x_assum `proceed_create` kall_tac
  >> Cases_on `s.contexts` >- gvs[]
  >> Cases_on `se.contexts` >- gvs[]
  >> Cases_on `s'.contexts` >- gvs[]
  >> Cases_on `t''` >- gvs[]
  >> gvs[]
  >> conj_tac >- (gen_tac >> Cases_on `i` >> simp[])
  >> conj_tac >- metis_tac[SUBSET_TRANS]
  >> conj_tac >- metis_tac[SUBSET_TRANS]
  >> conj_tac >- (gen_tac >> Cases_on `i` >> simp[])
  >> Cases_on `t` >> gvs[]
  >> simp[LAST_EL]
QED

(* -------------------------------------------------------------------------
 * Stack room for CALL/CREATE growth.
 * ------------------------------------------------------------------------- *)

Theorem step_call_grow_parent_stack_room:
  wf_context (FST (HD s.contexts)) ∧ step_call op s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH (FST (HD (TL s'.contexts))).stack < stack_limit
Proof
  simp[step_call_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> `0 < n` by (simp[Abbr`n`] >> Cases_on `call_has_value op` >> simp[])
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `LENGTH (FST (HD sp.contexts)).stack < stack_limit ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              wf_context_def, ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    >> pairarg_tac >> gvs[]
    (* Peel memory_expansion_info *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> impl_keep_tac >- (strip_tac >> gvs[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s2.contexts)).stack < stack_limit` by gvs[]
    (* Peel consume_gas *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s3.contexts)).stack < stack_limit` by gvs[]
    (* Peel expand_memory *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s4.contexts)).stack < stack_limit` by gvs[]
    (* Peel access/read prefix pieces, following step_call_push_structure. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> impl_keep_tac >- (CASE_TAC >> simp[] >> irule preserves_head_stack_bind
                         >> simp[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s5.contexts)).stack < stack_limit` by gvs[]
    >> pairarg_tac >> gvs[ignore_bind_def]
    (* EIP-8037: the opcode's execution gas, before the creation charge. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s6.contexts)).stack < stack_limit` by gvs[]
    (* EIP-8037: the account-creation charge, before the child's grant. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[charge_new_account_def] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sc.contexts)).stack < stack_limit` by gvs[]
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s7.contexts)).stack < stack_limit` by gvs[]
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s8.contexts)).stack < stack_limit` by gvs[]
    (* The grant is computed after the charge, so the 63/64 rule sees the
       execution gas a spill thinned. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s9.contexts)).stack < stack_limit` by gvs[]
    >> pairarg_tac >> gvs[ignore_bind_def]
    (* EIP-8037: the child's grant, charged in execution gas too. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s9 sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sd.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_callee *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s0.contexts)).stack < stack_limit` by gvs[]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[Ntimes COND_RATOR 2]
    >> Cases_on`bbb` >> gs[]
    >- (
      drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
      >> simp[])
    (* Peel set_return_data via ignore_bind *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sa.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sb.contexts)).stack < stack_limit` by gvs[]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> Cases_on`bbb` >> gs[]
    >- (
      drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
      >> simp[])
    >> drule_all proceed_call_push_structure
    >> strip_tac
    >> gvs[])
  >> (
    (* If pop_stack failed, the state did not grow. *)
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def,bind_def,assert_def,set_current_context_def,
            return_def,fail_def,AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_create_grow_parent_stack_room:
  wf_context (FST (HD s.contexts)) ∧ step_create two s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH (FST (HD (TL s'.contexts))).stack < stack_limit
Proof
  simp[step_create_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> `0 < n` by (simp[Abbr`n`] >> Cases_on `two` >> simp[])
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `LENGTH (FST (HD sp.contexts)).stack < stack_limit ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              wf_context_def, ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    (* Peel memory_expansion_info *)
    >> strip_tac
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> impl_keep_tac >- (strip_tac >> gvs[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s2.contexts)).stack < stack_limit` by gvs[]
    (* Peel consume_gas *)
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s3.contexts)).stack < stack_limit` by gvs[]
    (* Peel expand_memory *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s4.contexts)).stack < stack_limit` by gvs[]
    (* Peel read_memory *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s5.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_callee *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s6.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_accounts *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s7.contexts)).stack < stack_limit` by gvs[]
    (* Peel assert (code length) via ignore_bind *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s8.contexts)).stack < stack_limit` by gvs[]
    (* Peel assert_not_static *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sb.contexts)).stack < stack_limit` by gvs[]
    (* Peel set_return_data *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sb sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH sb.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sc.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sd.contexts)).stack < stack_limit` by gvs[]
    (* Split the preliminary failure condition. *)
    >> qmatch_asmsub_abbrev_tac`COND preliminaryFailure _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND preliminaryFailure _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> strip_tac
    (* Peel access_address *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd sx`
    >> `sx.contexts ≠ [] ∧ LENGTH sx.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sx.contexts)).stack < stack_limit` by gvs[]
    (* Peel ensure_storage_in_domain *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sx sy`
    >> `sy.contexts ≠ [] ∧ LENGTH sy.contexts = LENGTH sx.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sy.contexts)).stack < stack_limit` by gvs[]
    (* EIP-8037: the destination's creation, charged before the child's
       grant is withheld so a spill thins what is withheld. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[charge_new_account_def] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sy sz`
    >> `sz.contexts ≠ [] ∧ LENGTH sz.contexts = LENGTH sy.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sz.contexts)).stack < stack_limit` by gvs[]
    (* Peel withhold_create_gas *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[preserves_same_frame_state_gas_meter] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sz se`
    >> `se.contexts ≠ [] ∧ LENGTH se.contexts = LENGTH sz.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD se.contexts)).stack < stack_limit` by gvs[]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND bbb _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists) >> simp[])
    >> strip_tac
    >> drule_all proceed_create_push_structure
    >> strip_tac
    >> gvs[])
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_call_grow_parent_gas_monotone:
  step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed ≤ (FST (EL 1 s'.contexts)).gasUsed
Proof
  simp[step_call_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed ≤ (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    >> pairarg_tac >> gvs[]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s2.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s3.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s4.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> impl_keep_tac >- (CASE_TAC >> simp[] >> irule preserves_head_gas_mono_bind >> simp[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s5.contexts)).gasUsed` by decide_tac
    >> pairarg_tac >> gvs[ignore_bind_def]
    (* EIP-8037: the opcode's own execution gas, the creation charge in state
       gas, the static check and the memory expansion all come before the
       child's grant is read. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s6.contexts)).gasUsed` by decide_tac
    (* EIP-8037: the recipient's creation, charged in state gas before the
       child's grant is computed so a spill thins what the 63/64 rule sees. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s7.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s8.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s9.contexts)).gasUsed` by decide_tac
    (* The grant is computed after the charge, so the 63/64 rule sees the
       execution gas a spill thinned. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> pairarg_tac >> gvs[ignore_bind_def]
    >> rename1`same_frame_rel s9 sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sc.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sd.contexts)).gasUsed` by decide_tac
    (* Peel get_callee *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s0.contexts)).gasUsed` by decide_tac
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[Ntimes COND_RATOR 2]
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sa.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sb.contexts)).gasUsed` by decide_tac
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> drule_all proceed_call_push_structure
    >> strip_tac
    >> `EL 1 s'.contexts = HD (TL s'.contexts)` by
         (Cases_on `s'.contexts` >> gvs[EL_CONS])
    >> simp[] )
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_create_grow_parent_gas_monotone:
  step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed ≤ (FST (EL 1 s'.contexts)).gasUsed
Proof
  simp[step_create_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed ≤ (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    (* memory_expansion_info *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s2.contexts)).gasUsed` by decide_tac
    (* consume_gas *)
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s3.contexts)).gasUsed` by decide_tac
    (* expand_memory *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s4.contexts)).gasUsed` by decide_tac
    (* read_memory *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s5.contexts)).gasUsed` by decide_tac
    (* get_callee *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s6.contexts)).gasUsed` by decide_tac
    (* get_accounts *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s7.contexts)).gasUsed` by decide_tac
    (* assert code length *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s8.contexts)).gasUsed` by decide_tac
    (* assert_not_static *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sa.contexts)).gasUsed` by decide_tac
    (* set_return_data *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sb.contexts)).gasUsed` by decide_tac
    (* get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sb sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH sb.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sd.contexts)).gasUsed` by decide_tac
    (* Split the preliminary failure condition. *)
    >> qmatch_asmsub_abbrev_tac`COND preliminaryFailure _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND preliminaryFailure _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> strip_tac
    (* access_address *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd sx`
    >> `sx.contexts ≠ [] ∧ LENGTH sx.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sx.contexts)).gasUsed` by decide_tac
    (* ensure_storage_in_domain *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sx sy`
    >> `sy.contexts ≠ [] ∧ LENGTH sy.contexts = LENGTH sx.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sy.contexts)).gasUsed` by decide_tac
    (* EIP-8037: the destination's creation, charged in state gas before the
       child's grant is withheld so a spill thins what is withheld. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sy sz`
    >> `sz.contexts ≠ [] ∧ LENGTH sz.contexts = LENGTH sy.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sz.contexts)).gasUsed` by decide_tac
    (* EIP-8037: the child's grant is withheld after the charge, so the
       63/64 rule sees the gas a spill thinned. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[]
    >> (impl_tac >- (simp[withhold_create_gas_def] >>
         irule preserves_head_gas_mono_bind >> simp[] >> gen_tac >>
         irule preserves_head_gas_mono_ignore_bind >> simp[]))
    >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sz se`
    >> `se.contexts ≠ [] ∧ LENGTH se.contexts = LENGTH sz.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD se.contexts)).gasUsed` by decide_tac
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND bbb _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists) >> simp[])
    >> strip_tac
    >> drule_all proceed_create_push_structure
    >> strip_tac
    >> `EL 1 s'.contexts = HD (TL s'.contexts)` by
         (Cases_on `s'.contexts` >> gvs[EL_CONS])
    >> simp[])
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem call_gas_stipend_le_consumed:
  (if 0 < value then call_stipend else 0) ≤ otherCost + memoryCost ∧
  call_gas value gas gasLeft memoryCost otherCost = (dynamicGas, stipend) ⇒
  stipend ≤ dynamicGas + memoryCost
Proof
  rw[call_gas_def]
QED

Theorem proceed_call_parent_gas_ok:
  proceed_call op sender address value argsOffset argsSize code stipend outputTo s = (r, s') ∧
  s.contexts ≠ [] ∧
  oldGas + stipend ≤ (FST (HD s.contexts)).gasUsed ⇒
    oldGas +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def, drain_state_gas_reservoir_def,
          bind_def, ignore_bind_def, get_current_context_def,
          set_current_context_def, return_def, get_accounts_def]
  >> simp[bind_def, get_rollback_def, return_def]
  >> simp[read_memory_def, bind_def, return_def, get_current_context_def]
  >> qmatch_goalsub_abbrev_tac `COND transfer _ _`
  >> Cases_on `transfer`
  >> qpat_x_assum `Abbrev _` kall_tac
  >> (simp[update_accounts_def, return_def]
  >> qmatch_goalsub_abbrev_tac `get_caller s1`
  >> `s1.contexts <> [] /\
      (FST (HD s1.contexts)).gasUsed = (FST (HD s.contexts)).gasUsed`
       by simp[Abbr `s1`]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_value_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_static_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_static_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> TOP_CASE_TAC
  >> drule push_context_effect >> strip_tac >> gvs[]
  >> qmatch_asmsub_abbrev_tac `push_context (ctx, _) s1`
  >> reverse IF_CASES_TAC
  >- (
    rw[return_def]
    >> gvs[Abbr`ctx`, initial_context_def, initial_msg_params_def])
  >> strip_tac
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles addr ss = (_, s')`
  >> `ss.contexts ≠ []` by simp[Abbr`ss`]
  >> qmatch_asmsub_abbrev_tac `dpa ss = (_,_)`
  >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
  >> pop_assum mp_tac
  >> rewrite_tac[preserves_same_frame_def]
  >> disch_then drule
  >> simp[same_frame_rel_def]
  >> strip_tac
  >> gvs[Abbr`ctx`, Abbr`ss`, initial_context_def, initial_msg_params_def]
  >> Cases_on`s'.contexts` >> gvs[])
QED

Theorem proceed_create_parent_gas_ok:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ∧
  oldGas + cappedGas ≤ (FST (HD s.contexts)).gasUsed ⇒
    oldGas +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def, drain_state_gas_reservoir_def,
          get_current_context_def, set_current_context_def,
          bind_def, ignore_bind_def, return_def, get_accounts_def]
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  >> strip_tac
  >> drule push_context_effect >> strip_tac
  >> gvs[initial_context_def, initial_msg_params_def]
  >> qspec_then`s.contexts`FULL_STRUCT_CASES_TAC SNOC_CASES >> gvs[]
  >> gvs[set_last_accounts_def,update_account_def]
  >> Cases_on`l` >> gvs[]
QED

Theorem proceed_call_parent_unused_gas_ok:
  proceed_call op sender address value argsOffset argsSize code stipend outputTo s = (r,s') /\
  s.contexts <> [] /\ oldGas + stipend <= (FST (HD s.contexts)).gasUsed ==>
  oldGas + frame_unused_gas (FST (HD s'.contexts)) <=
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  qhdtm_x_assum `proceed_call` mp_tac >>
  simp[proceed_call_def, drain_state_gas_reservoir_def,
       bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def, get_rollback_def,
       read_memory_def, get_caller_def, get_value_def, get_static_def,
       get_accounts_def] >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  (simp[update_accounts_def, return_def, push_context_def, bind_def] >>
   qmatch_goalsub_abbrev_tac `(if _ then _ else _) ss` >>
   Cases_on `fIN address precompile_addresses`
   >- (simp[] >> strip_tac >>
       qspec_then `address` mp_tac
         (GEN_ALL (INST_TYPE [alpha |-> ``:unit``] decreases_gas_dispatch_precompiles)) >>
       rewrite_tac[decreases_gas_def] >>
       disch_then (qspec_then `ss` mp_tac) >>
       qhdtm_x_assum `dispatch_precompiles`
         (fn th => pure_rewrite_tac[th]) >>
       simp[Abbr `ss`] >> strip_tac >>
       gvs[initial_context_def, initial_msg_params_def, frame_unused_gas_def]) >>
   simp[return_def, Abbr `ss`, initial_context_def, initial_msg_params_def,
        frame_unused_gas_def] >> strip_tac >> gvs[])
QED

Theorem proceed_create_parent_unused_gas_ok:
  proceed_create senderAddress address value code cappedGas s = (r,s') /\
  s.contexts <> [] /\ oldGas + cappedGas <= (FST (HD s.contexts)).gasUsed ==>
  oldGas + frame_unused_gas (FST (HD s'.contexts)) <=
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >> qhdtm_x_assum `proceed_create` mp_tac >>
  simp[proceed_create_def, drain_state_gas_reservoir_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, update_accounts_def,
       get_rollback_def, get_original_def, set_original_def,
       get_accounts_def] >>
  strip_tac >> drule push_context_effect >> strip_tac >>
  gvs[initial_context_def, initial_msg_params_def, frame_unused_gas_def] >>
  qspec_then `s.contexts` FULL_STRUCT_CASES_TAC SNOC_CASES >> gvs[] >>
  gvs[set_last_accounts_def, update_account_def] >> Cases_on `l` >> gvs[]
QED

Theorem step_call_grow_parent_weight_ok:
  (!op sender address value argsOffset argsSize code stipend outputTo t r u b.
    proceed_call op sender address value argsOffset argsSize code stipend outputTo t = (r,u) /\
    t.contexts <> [] /\ b + stipend <= (FST (HD t.contexts)).gasUsed ==>
    b + weight (FST (HD u.contexts)) <= (FST (EL 1 u.contexts)).gasUsed) ==>
  wf_state s ∧ step_call op s = (r, s') ∧
  is_call op ∧ (op ≠ Create ∧ op ≠ Create2) ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed + weight (FST (HD s'.contexts)) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  disch_then (mk_asm "coverage") >> simp[step_call_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed = (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    >> pairarg_tac >> gvs[]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> simp[] >> strip_tac
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> impl_keep_tac
    >- (CASE_TAC >> simp[] >> irule preserves_head_gas_mono_bind >> simp[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* EIP-8037: the opcode's own execution gas is charged before the
       recipient's creation, so the grant the 63/64 rule applies to is what
       is left of it. *)
    >> pairarg_tac >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> qmatch_asmsub_abbrev_tac `consume_gas execCost s5 = _`
    >> `((FST (HD s.contexts)).gasUsed + execCost ≤
          (FST (HD s6.contexts)).gasUsed)` by (
       qhdtm_x_assum`consume_gas`mp_tac >>
       simp[consume_gas_def, bind_def,get_current_context_def,return_def] >>
       simp[assert_def,ignore_bind_def,bind_def,CaseEq"bool",CaseEq"sum"] >>
       simp[set_current_context_def,return_def] >> strip_tac >>
       gvs[] )
    (* EIP-8037: the recipient's creation, in state gas, before the grant. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* The grant is computed after the charge, so the 63/64 rule sees the
       execution gas a spill thinned. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> pairarg_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[]
    >> qpat_x_assum`_ _ = (_,stipend)`(markerLib.ASSUME_NAMED_TAC"cg")
    >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s9 sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> qmatch_asmsub_abbrev_tac `consume_gas grantCost s9 = _`
    >> `((FST (HD s9.contexts)).gasUsed + grantCost ≤
          (FST (HD sd.contexts)).gasUsed)` by (
       qhdtm_x_assum`consume_gas`mp_tac >>
       simp[consume_gas_def, bind_def,get_current_context_def,return_def] >>
       simp[assert_def,ignore_bind_def,bind_def,CaseEq"bool",CaseEq"sum"] >>
       simp[set_current_context_def,return_def] >> strip_tac >>
       gvs[] )
    (* EIP-8037: the two execution charges are additive, so what the prefix
       spends is the opcode's own cost plus the child's grant. *)
    >> `((FST (HD s.contexts)).gasUsed + (execCost + grantCost) ≤
          (FST (HD sd.contexts)).gasUsed)` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[Ntimes COND_RATOR 2]
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> asm "coverage" drule
    >> disch_then (irule o ONCE_REWRITE_RULE [ADD_COMM])
    >> simp[]
    >> qmatch_goalsub_abbrev_tac`stipend + spg <= sbg`
    >> qpat_x_assum`_ + spg <= _`mp_tac
    >> qmatch_goalsub_abbrev_tac`_ <= s7g`
    >> `s7g <= sbg` by simp[]
    (* EIP-8037: the parent spends its own execution gas and then the whole
       grant, and the stipend the child carries is the value transfer's own
       cost, already inside that execution gas. *)
    >> `s7g + callGas <= sbg` by decide_tac
    >> `stipend <= execCost + callGas` suffices_by decide_tac
    >> qunabbrev_tac`execCost`
    >> markerLib.LABEL_ASSUM"cg"assume_tac
    >> qhdtm_x_assum`call_gas`mp_tac
    >> simp[call_gas_def, call_stipend_def, call_value_cost_def]
    >> strip_tac
    >> qpat_x_assum`_ = stipend`(fn th => SUBST_ALL_TAC (SYM th))
    >> Cases_on`0 < (if 0 < if call_has_value op then 1 else 0
                       then w2n (EL 2 args) else 0)`
    >> gvs[] >> decide_tac )
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_call_grow_parent_gas_ok:
  wf_state s ∧ step_call op s = (r, s') ∧
  is_call op ∧ (op ≠ Create ∧ op ≠ Create2) ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >>
  irule (BETA_RULE (Q.INST [`weight` |-> `\c. c.msgParams.gasLimit - c.gasUsed`]
    step_call_grow_parent_weight_ok)) >>
  metis_tac[proceed_call_parent_gas_ok]
QED

Theorem step_create_grow_parent_weight_ok:
  (!senderAddress address value code cappedGas t r u b.
    proceed_create senderAddress address value code cappedGas t = (r,u) /\
    t.contexts <> [] /\ b + cappedGas <= (FST (HD t.contexts)).gasUsed ==>
    b + weight (FST (HD u.contexts)) <= (FST (EL 1 u.contexts)).gasUsed) ==>
  wf_state s ∧ step_create two s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed + weight (FST (HD s'.contexts)) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  disch_then (mk_asm "coverage") >> simp[step_create_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed ≤ (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    (* Same peel as gas monotonicity, with additive cappedGas reservation. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* assert code length *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* assert_not_static *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* set_return_data *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sb sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH sb.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* Split the preliminary failure condition. *)
    >> qmatch_asmsub_abbrev_tac`COND preliminaryFailure _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND preliminaryFailure _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> strip_tac
    (* access_address *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd sx`
    >> `sx.contexts ≠ [] ∧ LENGTH sx.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* ensure_storage_in_domain *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sx sy`
    >> `sy.contexts ≠ [] ∧ LENGTH sy.contexts = LENGTH sx.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* EIP-8037: the destination's creation, charged before the child's
       grant is withheld so a spill thins what is withheld. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sy sz`
    >> `sz.contexts ≠ [] ∧ LENGTH sz.contexts = LENGTH sy.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* withhold_create_gas: the additive execution-gas reservation. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[]
    >> (impl_tac >- (simp[withhold_create_gas_def] >>
         irule preserves_head_gas_mono_bind >> simp[] >> gen_tac >>
         irule preserves_head_gas_mono_ignore_bind >> simp[]))
    >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sz se`
    >> `se.contexts <> [] /\ LENGTH se.contexts = LENGTH sz.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> qpat_x_assum `withhold_create_gas sz = (INL _, se)` mp_tac
    >> simp[withhold_create_gas_def, get_gas_left_def,
            get_current_context_def, bind_def, ignore_bind_def, return_def]
    >> strip_tac >> gvs[AllCaseEqs()]
    >> rename1 `consume_gas cappedGas sz = _`
    >> `(FST (HD sz.contexts)).gasUsed + cappedGas <=
        (FST (HD se.contexts)).gasUsed` by
         (drule consume_gas_head_gas_add_ge >> simp[])
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND bbb _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists) >> simp[])
    >> strip_tac
    >> asm "coverage" (irule o ONCE_REWRITE_RULE [ADD_COMM])
    >> goal_assum $ drule_at Any
    >> simp[]
    (* EIP-8037: the grant is withheld only after the destination's creation
       is charged, so both come out of the same execution gas. *)
    >> decide_tac)
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_create_grow_parent_gas_ok:
  wf_state s ∧ step_create two s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >>
  irule (BETA_RULE (Q.INST [`weight` |-> `\c. c.msgParams.gasLimit - c.gasUsed`]
    step_create_grow_parent_weight_ok)) >>
  metis_tac[proceed_create_parent_gas_ok]
QED

Theorem step_call_grow_parent_unused_gas_ok:
  wf_state s /\ step_call op s = (r,s') /\
  is_call op /\ (op <> Create /\ op <> Create2) /\
  s.contexts <> [] /\ LENGTH s'.contexts > LENGTH s.contexts ==>
  (FST (HD s.contexts)).gasUsed + frame_unused_gas (FST (HD s'.contexts)) <=
  (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >>
  irule (Q.INST [`weight` |-> `frame_unused_gas`] step_call_grow_parent_weight_ok) >>
  metis_tac[proceed_call_parent_unused_gas_ok]
QED

Theorem step_create_grow_parent_unused_gas_ok:
  wf_state s /\ step_create two s = (r,s') /\
  s.contexts <> [] /\ LENGTH s'.contexts > LENGTH s.contexts ==>
  (FST (HD s.contexts)).gasUsed + frame_unused_gas (FST (HD s'.contexts)) <=
  (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >>
  irule (Q.INST [`weight` |-> `frame_unused_gas`] step_create_grow_parent_weight_ok) >>
  metis_tac[proceed_create_parent_unused_gas_ok]
QED

Theorem step_inner_grow_parent_unused_gas_ok:
  step_inner s = (r,s') /\ wf_state s /\ s.contexts <> [] /\
  LENGTH s'.contexts > LENGTH s.contexts ==>
  frame_unused_gas (FST (HD s'.contexts)) <= (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >>
  gvs[step_inner_def, bind_def, get_current_context_def, COND_RATOR,
      fail_def, return_def, CaseEq "bool", CaseEq "prod",
      option_CASE_rator, CaseEq "option", ignore_bind_def]
  >- (`preserves_same_frame (step_inst Stop)` by simp[] >>
      drule_all psf_imp_length_contexts_preserved >> simp[])
  >- (`preserves_same_frame (step_inst Invalid)` by simp[] >>
      drule_all psf_imp_length_contexts_preserved >> simp[]) >>
  gvs[CaseEq "sum", CaseEq "prod"]
  >- (mp_tac preserves_same_frame_inc_pc_or_jump >>
      rewrite_tac[preserves_same_frame_def] >>
      disch_then drule >> simp[] >>
      (impl_tac >- metis_tac[step_inst_preserves_nonempty_contexts, SND]) >>
      strip_tac >>
      `is_call op` by
        (drule step_inst_inl_grew_is_call >> gvs[same_frame_rel_def]) >>
      gvs[inc_pc_or_jump_def, return_def] >>
      Cases_on `op = Create \/ op = Create2`
      >- (gvs[step_inst_def] >>
          drule_all step_create_grow_parent_unused_gas_ok >> decide_tac) >>
      `step_inst op s = step_call op s` by
        (Cases_on `op` >> gvs[step_inst_def, is_call_def]) >>
      gvs[] >> drule_all step_call_grow_parent_unused_gas_ok >> decide_tac) >>
  drule step_inst_inr_grew_is_call_family >> simp[] >> strip_tac >>
  `step_inst op s = step_call op s` by gvs[step_inst_def] >>
  gvs[] >>
  drule_at (Pat `step_call`) step_call_grow_parent_unused_gas_ok >>
  simp[is_call_def] >> decide_tac
QED

Theorem step_grow_parent_unused_gas_ok:
  step s = (r,s') /\ wf_state s /\ s.contexts <> [] /\
  outputTo_consistent_stack s /\ LENGTH s'.contexts > LENGTH s.contexts ==>
  frame_unused_gas (FST (HD s'.contexts)) <= (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >> qhdtm_x_assum `step` mp_tac >>
  simp[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner s` >> Cases_on `q`
  >- (simp[] >> strip_tac >> gvs[] >>
      drule_all step_inner_grow_parent_unused_gas_ok >> simp[]) >>
  simp[] >> strip_tac >> rename1 `handle_step e sm = (_,s')` >>
  `same_frame_or_grow step_inner` by simp[] >>
  `LENGTH sm.contexts >= LENGTH s.contexts` by
    (drule_all same_frame_or_grow_length >> simp[]) >>
  `sm.contexts <> []` by (strip_tac >> gvs[] >> Cases_on `s.contexts` >> gvs[]) >>
  Cases_on `LENGTH sm.contexts = LENGTH s.contexts`
  >- (drule handle_step_shrinks_by_one >> simp[]) >>
  `LENGTH sm.contexts > LENGTH s.contexts` by simp[] >>
  `outputTo_consistent s` by metis_tac[outputTo_consistent_stack_imp_consistent] >>
  `~vfm_abort e` by
    (irule step_inner_inr_grow_not_abort >>
     qpat_x_assum `step_inner s = _` mp_tac >> simp[step_inner_def] >>
     strip_tac >> goal_assum $ drule_at Any >> simp[]) >>
  `LENGTH sm.contexts = LENGTH s.contexts + 1` by
    (qpat_x_assum `step_inner s = _` mp_tac >> simp[step_inner_def] >>
     strip_tac >> drule_then drule step_inner_grows_by_exactly_one >> simp[]) >>
  `LENGTH sm.contexts >= 2` by (Cases_on `s.contexts` >> gvs[]) >>
  drule_at (Pat `handle_step`) handle_step_not_abort_pops >> simp[] >>
  `EVERY (wf_context o FST) sm.contexts` suffices_by
    (rpt (pop_assum kall_tac) >> rw[EVERY_MEM, EXISTS_MEM, o_DEF] >> metis_tac[]) >>
  mp_tac decreases_gas_cred_step_inner >> gvs[decreases_gas_cred_def] >>
  disch_then (qspec_then `s` mp_tac) >> rw[] >> gvs[wf_state_def]
QED

(* Named facts about the pre-handler inner step. *)

(* Full-step push structure: storage/access shape plus parent stack/gas facts. *)
Theorem step_push_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧ wf_state s ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH s'.contexts = LENGTH s.contexts + 1 ∧
    (* Storage preservation for s'.rollback, except that CREATE clears the
       storage of the address it creates *)
    (∀a. (lookup_account a s'.rollback.accounts).storage =
         (lookup_account a s.rollback.accounts).storage ∨
         (lookup_account a s'.rollback.accounts).storage = empty_storage ∧
         ¬account_already_created (lookup_account a s.rollback.accounts)) ∧
    toSet s.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys ∧
    (* saved rollback storage; CREATE's old-LAST exception is excluded *)
    (∀i. i < LENGTH s.contexts ⇒
         (∀a. (lookup_account a (SND (EL i s'.contexts)).accounts).storage =
              (lookup_account a (if i = 0 then s.rollback
                                 else SND (EL (i-1) s.contexts)).accounts).storage)) ∧
    (∀i. i < LENGTH s'.contexts ⇒
         toSet (if i = 0 then s.rollback
                else SND (EL (i-1) s.contexts)).accesses.storageKeys ⊆
           toSet (SND (EL i s'.contexts)).accesses.storageKeys) ∧
    (* saved parent / shifted tail *)
    MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
    LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit ∧
    (FST (EL 1 s'.contexts)).gasUsed ≥ (FST (HD s.contexts)).gasUsed ∧
    (FST (HD s.contexts)).gasUsed +
      ((FST (HD s'.contexts)).msgParams.gasLimit -
       (FST (HD s'.contexts)).gasUsed) ≤
      (FST (EL 1 s'.contexts)).gasUsed ∧
    (* parent msgParams *)
    (LENGTH s.contexts ≥ 1 ⇒
       (FST (EL 1 s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams) ∧
    (* new child outputTo consistency *)
    outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
    (* shifted outputTo consistency *)
    (∀i. i < LENGTH s.contexts ⇒
         outputTo_consistent_ctx (FST (EL i s.contexts)) ⇒
         outputTo_consistent_ctx (FST (EL (i+1) s'.contexts)))
Proof
  rpt gen_tac >> strip_tac
  (* Unfold step = handle inner handle_step *)
  >> qpat_x_assum `step s = _` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `inner s`
  >> Cases_on `inner s` >> Cases_on `q`
  (* Case: inner returned INL - step returns inner's result *)
  >- (
    simp[] >> strip_tac >> gvs[]
    (* inner = get_ctx; step_inst; inc_pc_or_jump *)
    >> gvs[Abbr`inner`, bind_def,AllCaseEqs()]
    >> gvs[get_current_context_def, return_def, fail_def, bind_def]
    >> gvs[option_CASE_rator,CaseEq"option"]
    >> gvs[COND_RATOR, CaseEq"bool"]
    (* Case: NONE, code ≤ pc, step_inst Stop *)
    >~ [`step_inst Stop`]
    >- (
      `preserves_same_frame (step_inst Stop)` by simp[]
      >> drule_all psf_imp_length_contexts_preserved
      >> simp[])
    (* NONE: step_inst Invalid *)
    >~ [`step_inst Invalid`]
    >- (
      `preserves_same_frame (step_inst Invalid)` by simp[]
      >> drule_all psf_imp_length_contexts_preserved
      >> simp[])
    (* SOME op: step_inst op; inc_pc_or_jump op *)
    >> gvs[ignore_bind_def, bind_def]
    >> gvs[AllCaseEqs()]
    >> rename1 `step_inst op s0 = (INL (), s1)`
    >> drule_at Any psf_imp_length_contexts_preserved
    >> simp[]
    >> impl_keep_tac >- (strip_tac >>
         gvs[inc_pc_or_jump_def,COND_RATOR,AllCaseEqs(),return_def] >>
         gvs[bind_def,get_current_context_def,fail_def,AllCaseEqs()] )
    >> strip_tac
    >> `LENGTH s1.contexts > LENGTH s0.contexts` by simp[]
    (* By step_inst_inl_grew_is_call, is_call op *)
    >> `is_call op` by metis_tac[step_inst_inl_grew_is_call]
    (* For is_call, inc_pc_or_jump = return (), so s' = s1 *)
    >> `r' = s1` by (
         gvs[inc_pc_or_jump_def, return_def, COND_RATOR, CaseEq"bool"])
    >> gvs[]
    >> `outputTo_consistent s0` by (
         gvs[outputTo_consistent_def, outputTo_consistent_stack_def]
         >> Cases_on`s0.contexts`
         >> gvs[outputTo_consistent_ctx_def])
    (* Case split on which call/create op *)
    >> Cases_on `∃two. step_inst op s0 = step_create two s0`
    >- (
      (* CREATE/CREATE2 case *)
      gvs[] >> pop_assum(assume_tac o SYM) >>
      (* Use step_create lemmas *)
      drule_then drule step_create_grows_by_exactly_one
      >> simp[] >> strip_tac
      (* CREATE either leaves the storage object alone or clears it. *)
      >> conj_tac
      >- (drule step_create_storage_object >> simp[] >> metis_tac[])
      (* Use step_create_push_structure *)
      >> drule step_create_push_structure
      >> simp[]
      >> strip_tac
      >> drule_then drule step_create_pushed_rb_storage
      >> simp[] >> strip_tac
      >> conj_tac
      >- ( Cases >> simp[] >> Cases_on`r'.contexts` >> gvs[] )
      >> conj_tac >- ( Cases >> gvs[] >> Cases_on`r'.contexts` >> gvs[] )
      >> drule_at Any step_create_grow_parent_stack_room
      >> impl_tac >- ( gvs[wf_state_def] >> Cases_on`s0.contexts` >> gvs[] )
      >> strip_tac
      >> conj_tac >- (
        qmatch_goalsub_rename_tac`EL 1 rr.contexts` >>
        Cases_on`rr.contexts` >> gvs[] )
      >> Cases_on`s0.contexts` >> gvs[]
      >> Cases_on`r'.contexts` >> gvs[]
      >> Cases_on`t'` >> gvs[]
      >> drule step_create_grow_parent_gas_monotone
      >> simp[] >> strip_tac
      >> drule_at(Pat`step_create`) step_create_grow_parent_gas_ok
      >> simp[] >> strip_tac
      >> Cases >> gvs[EL_CONS]
      >- ( simp[outputTo_consistent_ctx_def] )
      >> gvs[PRE_SUB1,ADD1]
      >> simp[outputTo_consistent_ctx_def]
      >> gvs[LIST_EQ_REWRITE,EL_MAP])
    >> (
      (* CALL family case *)
      `step_inst op s0 = step_call op s0`
      by (Cases_on`op` >> gvs[step_inst_def, is_call_def])
      (* Use step_call lemmas *)
      >> gvs[]
      >> drule_then drule step_call_grows_by_exactly_one
      >> simp[] >> strip_tac
      (* s1.rollback storage preserved *)
      >> drule(REWRITE_RULE[preserves_storage_def]preserves_storage_step_call)
      >> simp[lookup_storage_def, FUN_EQ_THM]
      >> strip_tac
      >> drule_all step_call_pushed_rb_storage
      >> strip_tac
      (* Use step_call_push_structure *)
      >> drule_all step_call_push_structure
      >> strip_tac
      >> simp[]
      >> conj_tac
      >- (
        Cases >> gvs[ADD1] >>
        Cases_on`r'.contexts` >> gvs[EL_CONS,PRE_SUB1] >>
        Cases_on`s0.contexts` >> gvs[ADD1] >>
        Cases_on`t` >> gvs[ADD1] >>
        Cases_on`n` >> gvs[ADD1] )
      >> drule_at(Pat`step_call`)step_call_grow_parent_stack_room
      >> impl_tac >- ( gvs[wf_state_def] >> Cases_on`s0.contexts` >- gvs[] >>
                       simp[] >> fs[])
      >> strip_tac
      >> Cases_on`r'.contexts` >> gvs[EL_CONS, PRE_SUB1]
      >> Cases_on`t` >> gvs[EL_CONS, PRE_SUB1, ADD1]
      >> Cases_on`s0.contexts` >> gvs[EL_CONS, PRE_SUB1, ADD1]
      >> drule step_call_grow_parent_gas_monotone
      >> simp[] >> strip_tac
      >> drule_at(Pat`step_call`)step_call_grow_parent_gas_ok
      >> simp[]
      >> impl_tac >- (rpt strip_tac >> gs[step_inst_def])
      >> strip_tac >> gvs[]
      >> conj_tac >> Cases >> gvs[ADD1]
      >- ( Cases_on`n` >> gvs[] )
      >> gvs[outputTo_consistent_ctx_def]))
  (* Case: inner returned INR - handle_step runs *)
  >> simp[]
  >> rename1 `handle_step e r' = (_, s')`
  (* inner is same_frame_or_grow *)
  >> `same_frame_or_grow inner` by simp[Abbr`inner`]
  >> `LENGTH r'.contexts ≥ LENGTH s.contexts` by (
       drule_all same_frame_or_grow_length >> simp[])
  >> strip_tac
  >> `r'.contexts ≠ []` by (strip_tac >> gvs[] >> Cases_on`s.contexts` >> gvs[])
  (* Inner INR-grow cannot lead to full-step growth: non-abort handlers pop;
     aborts reraise and preserve the inner length. *)
  >> `LENGTH s'.contexts ≤ LENGTH s.contexts` suffices_by gvs[]
  >> Cases_on `LENGTH r'.contexts = LENGTH s.contexts` >- (
       drule handle_step_shrinks_by_one >> simp[])
  (* inner grew *)
  >> `LENGTH r'.contexts > LENGTH s.contexts` by simp[]
  >> `outputTo_consistent s` by
       metis_tac[outputTo_consistent_stack_imp_consistent]
  >> `¬vfm_abort e` by (
       irule step_inner_inr_grow_not_abort
       >> qexistsl_tac [`s`, `r'`] >> simp[Abbr`inner`])
  >> `0 < LENGTH s.contexts` by (Cases_on`s.contexts` >> gvs[])
  >> `LENGTH r'.contexts ≥ 2` by simp[]
  (* Inner grew by exactly 1 *)
  >> `LENGTH r'.contexts = LENGTH s.contexts + 1` by (
       qunabbrev_tac`inner` >>
       drule_then drule step_inner_grows_by_exactly_one >> gvs[])
  (* Need EVERY (wf_context o FST) r'.contexts to apply handle_step_not_abort_pops *)
  >> drule_at(Pat`handle_step`) handle_step_not_abort_pops
  >> gvs[]
  >> `decreases_gas_cred T 0 0 inner` suffices_by (
    gvs[decreases_gas_cred_def] >>
    disch_then(qspec_then`s`mp_tac) >> rw[] >>
    gvs[wf_state_def] >>
    gvs[EVERY_MEM] ) >>
  simp[Abbr`inner`] >>
  irule decreases_gas_cred_bind_mono >>
  qexistsl_tac[`T`,`F`] >> simp[] >> gen_tac >>
  rw[] >> CASE_TAC >> rw[] >>
  irule decreases_gas_cred_ignore_bind_mono >> rw[] >>
  qexistsl_tac[`F`,`T`] >> simp[]
QED

(* Full-step pop structure.  Rollback equality is weakened to storage equality
 * plus the matching accesses subset, because handle_create may change code. *)
(* EIP-8037 replacement for `step_inst_same_frame_gas_monotone`, which was
   false.  `credit_state_gas_refund` (`spec/vfmExecutionScript.sml:518-527`)
   takes `MIN n stateGasSpilled` out of the frame's `gasUsed`, and
   `step_sstore_gas_consumption` runs it before its charges (`:1016`, charges
   at `:1021-1022`), so a slot-clearing SSTORE on a frame that has already
   spilled can end below its starting `gasUsed`.  Checked witness (since
   removed with the other probes): the slot-clearing SSTORE on an
   already-spilled frame whose refund lands before the charges.

   The measure is what survives: the credit lowers `gasUsed` and the spill
   together and puts the excess in the reservoir, which `frame_unused_gas`
   does not count, so it leaves the measure alone; `charge_state_gas` moves both
   together on its spill branch; and `update_gas_refund` never touches
   `gasUsed`.  Inside a same-frame step the head's `frame_unused_gas` can
   therefore only fall, by `consume_gas`. *)
Theorem step_inst_same_frame_unused_gas_monotone:
   step_inst op s = (q, s') ∧
   same_frame_rel s s' ∧
   EVERY (wf_context o FST) s.contexts
   ⇒
     frame_unused_gas (FST (HD s'.contexts)) ≤
     frame_unused_gas (FST (HD s.contexts))
Proof
  strip_tac
  >> qspec_then`op`mp_tac(GEN_ALL decreases_gas_cred_step_inst)
  >> rewrite_tac[decreases_gas_cred_def]
  >> disch_then(qspec_then`s`mp_tac)
  >> simp[]
  >> gvs[same_frame_rel_def]
  >> Cases_on`s.contexts` >> gvs[]
  >> Cases_on`s'.contexts` >> gvs[]
  >> gvs[contexts_weight_def, unused_gas_def, LEX_DEF]
  >> strip_tac >> Cases_on `ISL q` >> gvs[]
QED

(* EIP-8037: this used to bound `new_head.gasUsed` by the parent's, less the
   child's leftover execution gas.  That bound is dropped rather than weakened:
   the frame whose meter pays the merge's spill repayment is the head of the
   intermediate state, which `step` does not name, so the repayment
   `MIN stateGasLeft stateGasSpilled` cannot be written in this statement's
   variables, and any existential over it would be satisfied by every value. *)
Theorem step_pop_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧
    EVERY (wf_context o FST) s.contexts ∧
    LENGTH s'.contexts < LENGTH s.contexts ⇒
    ∃new_head parent rest.
      s.contexts = HD s.contexts :: parent :: rest ∧
      s'.contexts = (new_head, SND parent) :: rest ∧
      new_head.msgParams = (FST parent).msgParams ∧
      ((toSet s.rollback.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a s.rollback.accounts).storage)) ∨
       (toSet (SND (HD s.contexts)).accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a (SND (HD s.contexts)).accounts).storage)))
Proof
  rpt strip_tac
  >> qpat_x_assum `step s = (r,s')` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `inner s`
  >> Cases_on `inner s` >> Cases_on `q` >> gvs[Abbr `inner`]
  >- (rpt strip_tac >> assume_tac same_frame_or_grow_step_inner
      >> drule_all same_frame_or_grow_length >> fs[])
  >> rpt strip_tac
  >> ASSUME_TAC same_frame_or_grow_step_inner
  >> `LENGTH r'.contexts >= LENGTH s.contexts`
       by (drule_all same_frame_or_grow_length >> fs[])
  >> `r'.contexts <> []` by (Cases_on `r'.contexts` >> fs[])
  >> `LENGTH s'.contexts + 1 >= LENGTH r'.contexts /\
      LENGTH s'.contexts <= LENGTH r'.contexts`
       by (drule handle_step_shrinks_by_one >> fs[])
  >> `LENGTH r'.contexts = LENGTH s.contexts` by decide_tac
  >> `same_frame_rel s r'` by (drule_all same_frame_or_grow_eq_length >> fs[])
  >> `LENGTH s.contexts >= 2` by (
       CCONTR_TAC >> fs[]
       >> `LENGTH s.contexts <= 1` by decide_tac
       >> `LENGTH s.contexts = 1` by decide_tac
       >> drule handle_step_preserves_length_1 >> fs[])
  >> `s.contexts = HD s.contexts :: TL s.contexts`
       by (Cases_on `s.contexts` >> fs[])
  >> `LENGTH (TL s.contexts) >= 1`
       by (Cases_on `TL s.contexts` >> fs[])
  >> `?parent rest. TL s.contexts = parent :: rest`
       by (Cases_on `TL s.contexts` >> fs[])
  >> `r'.contexts <> []` by fs[same_frame_rel_def]
  >> `TL r'.contexts = TL s.contexts /\ SND (HD r'.contexts) = SND (HD s.contexts)`
       by fs[same_frame_rel_def]
  >> `r'.contexts = (FST (HD r'.contexts), SND (HD s.contexts)) :: parent :: rest`
       by (Cases_on `r'.contexts` >> fs[] >> Cases_on `h` >> fs[])
  >> `LENGTH s'.contexts < LENGTH r'.contexts` by decide_tac
  (* Use paired lemma. Split its disjunction into two separate subgoals
     via strip_assume_tac, avoiding gvs contamination.
     DISJ1(r'): storage s'.rollback = storage r'.rollback
     DISJ2(r'): storage s'.rollback = storage (SND (HD r'.contexts)) *)
  >> Cases_on`y`
  >- (
    gvs[bind_def,get_current_context_def,return_def,fail_def]
    >> Cases_on`∃op. step_inst op s = (INR NONE, r')`
    >- (
      gvs[] >>
      drule_all step_inst_inr_preserves_storage >> rw[] >>
      drule_at_then(Pat`handle_step`)drule
        handle_step_pop_generic_gen_paired >>
      simp[] >>
      Cases_on`s.contexts` >> gvs[] >>
      Cases_on`r'.contexts` >> gvs[wf_context_def] >>
      Cases_on`s'.contexts` >> gvs[] >>
      disch_then (qx_choosel_then [`new_head`] strip_assume_tac) >>
      gvs[lookup_storage_def, FUN_EQ_THM] >>
      gvs[SUBSET_DEF,same_frame_rel_def] )
    >> gvs[option_CASE_rator, AllCaseEqs()]
    >> gvs[COND_RATOR,AllCaseEqs()]
    >> gvs[ignore_bind_def,bind_def,AllCaseEqs()]
    >> drule inc_pc_or_jump_inr_eq >> rw[] )
  >> gvs[handle_step_def]
  >> gvs[COND_RATOR,CaseEq"bool",reraise_def]
  >> gvs[handle_def,CaseEq"prod"]
  >> gvs[handle_create_reraises_when_some]
  >> gvs[reraise_def]
  >> gvs[bind_def, get_current_context_def, return_def]
  >> reverse(Cases_on`x = Reverted`)
  >- (
    drule_at(Pat`handle_exception`)handle_exception_pop_failure_rollback_gen >>
    simp[] >> Cases_on`r'.contexts` >> gvs[] >>
    Cases_on`h` >> gvs[] >> Cases_on`s'.contexts` >> gvs[] >>
    Cases_on`h` >> gvs[] >> strip_tac >>
    gvs[same_frame_rel_def] >>
    Cases_on`s.contexts` >> fs[] >>
    BasicProvers.VAR_EQ_TAC >> fs[] >>
    drule_at(Pat`handle_exception`)handle_exception_pop_generic_gen >>
    simp[] >> strip_tac >> gvs[]
  )
  >> drule_at(Pat`handle_exception`)handle_exception_pop_generic_gen
  >> simp[]
  >> Cases_on`r'.contexts` >> gvs[]
  >> Cases_on`h` >> gvs[]
  >> rpt strip_tac >> gvs[]
  >- (
    qexists_tac`parent` >> gvs[] >>
    gvs[same_frame_rel_def] >>
    Cases_on`s.contexts` >> fs[] >>
    disj1_tac >> qx_gen_tac`a` >>
    qmatch_asmsub_abbrev_tac`callee_local_changes callee` >>
    reverse(Cases_on`a = callee`) >- (
      gvs[callee_local_changes_def] ) >>
    gvs[bind_def,get_current_context_def,return_def,AllCaseEqs()] >>
    Cases_on`∃op. step_inst op s = (INR (SOME Reverted),r')`
    >- (
      gvs[] >>
      drule step_inst_inr_preserves_storage >>
      simp[lookup_storage_def, FUN_EQ_THM] ) >>
    gvs[option_CASE_rator,AllCaseEqs()] >>
    gvs[COND_RATOR,AllCaseEqs()] >>
    gvs[ignore_bind_def,bind_def,AllCaseEqs()] >>
    drule inc_pc_or_jump_inr_eq >> rw[]) >>
  Cases_on`s.contexts` >> fs[] >>
  gvs[wf_context_def] >>  gvs[same_frame_rel_def]
QED

(* -------------------------------------------------------------------------
 * Full wf_state preservation. Placed here because the strong wf_state
 * invariants use whole-step push/pop structure proved above.
 * ------------------------------------------------------------------------- *)

Theorem step_push_parent_stack_room:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts > LENGTH s.contexts
  ⇒ LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit
Proof
  rpt strip_tac
  >> drule step_push_structure
  >> gvs[]
  >> impl_tac >- gvs[wf_state_def]
  >> strip_tac
  >> simp[]
QED

Theorem step_preserves_stack_room_ok:
  wf_state s ⇒ stack_room_ok (SND (step s))
Proof
  strip_tac
  >> Cases_on `step s` >> simp[]
  >> rename1 `step s = (_, s')`
  >> rename1 `step s = (r, s')`
  >> Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (
    `outputTo_consistent s`
      by metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
    `same_frame_rel (zero_head_refunds s) s'` by
      metis_tac[step_same_frame, zero_head_refunds_def] >>
    irule same_frame_rel_preserves_stack_room_ok >>
    qexists_tac `zero_head_refunds s` >> simp[] >>
    gvs[wf_state_def, stack_room_ok_def, zero_head_refunds_def] >>
    Cases_on `s.contexts` >> gvs[])
  >> Cases_on `LENGTH s'.contexts > LENGTH s.contexts`
  >- (
    `LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit`
      by metis_tac[step_push_parent_stack_room] >>
    drule step_push_structure >> impl_tac >- gvs[wf_state_def] >>
    strip_tac >>
    gvs[stack_room_ok_def, wf_state_def] >>
    Cases_on `s'.contexts` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    rw[EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    gvs[])
  >> (
    `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac >>
    `outputTo_consistent_stack s` by gvs[wf_state_def] >>
    drule step_pop_structure >> simp[] >>
    impl_tac >- (rpt strip_tac >> gvs[wf_state_def]) >>
    strip_tac >>
    gvs[stack_room_ok_def, wf_state_def] >>
    Cases_on`s.contexts` >> gvs[]
  )
QED

Theorem same_frame_rel_preserves_outputTo_consistent_stack:
  same_frame_rel s s' ∧ outputTo_consistent_stack s ⇒
  outputTo_consistent_stack s'
Proof
  rw[outputTo_consistent_stack_def, same_frame_rel_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `s'.contexts` >> gvs[]
  >> gvs[outputTo_consistent_ctx_def]
QED

Theorem step_preserves_outputTo_consistent_stack:
  wf_state s ⇒ outputTo_consistent_stack (SND (step s))
Proof
  strip_tac
  >> Cases_on `step s` >> simp[]
  >> rename1 `step s = (_, s')`
  >> rename1 `step s = (r, s')`
  >> Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (
    `outputTo_consistent s`
    by metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
    `same_frame_rel (zero_head_refunds s) s'` by
      metis_tac[step_same_frame, zero_head_refunds_def] >>
    irule same_frame_rel_preserves_outputTo_consistent_stack >>
    qexists_tac `zero_head_refunds s` >> simp[] >>
    gvs[wf_state_def, outputTo_consistent_stack_def, zero_head_refunds_def] >>
    Cases_on `s.contexts` >> gvs[outputTo_consistent_ctx_def])
  >> Cases_on `LENGTH s'.contexts > LENGTH s.contexts`
  >- (
    drule step_push_structure >> impl_tac >- gvs[wf_state_def] >>
    strip_tac >>
    gvs[outputTo_consistent_stack_def, EVERY_MEM, MEM_EL] >>
    conj_tac >- (strip_tac >> gvs[]) >>
    rw[] >>
    Cases_on `n` >> gvs[] >- (
      Cases_on`s'.contexts` >> gvs[] ) >>
    simp[ADD1, EL_MAP] >> gvs[ADD1] >>
    first_x_assum irule >>
    gvs[wf_state_def,outputTo_consistent_stack_def] >>
    gvs[EVERY_EL, EL_MAP] ) >>
  `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac >>
  `outputTo_consistent_stack s` by gvs[wf_state_def] >>
  gvs[wf_state_def] >>
  drule_all step_pop_structure >>
  Cases_on `s.contexts` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on`s'.contexts` >> gvs[] >>
  strip_tac >> gvs[outputTo_consistent_stack_def] >>
  gvs[outputTo_consistent_ctx_def]
QED

Theorem step_push_parent_gas_ok:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  rpt strip_tac
  >> drule step_push_structure
  >> simp[]
  >> impl_tac >- gvs[wf_state_def]
  >> strip_tac >> simp[]
QED

Theorem step_unused_gas_nonincrease:
  s.contexts <> [] /\ step s = (r,s') ==>
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts)
Proof
  strip_tac >> mp_tac decreases_gas_cred_step >>
  rewrite_tac[decreases_gas_cred_def] >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[contexts_weight_def, LEX_DEF] >>
  Cases_on `r` >> gvs[] >> decide_tac
QED

Theorem gas_stack_ok_pop_transfer:
  gas_stack_ok s /\ s.contexts = child::parent::rest /\
  s'.contexts = new::rest /\
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts) ==>
  gas_stack_ok s'
Proof
  simp[gas_stack_ok_def, unused_gas_def] >> strip_tac >> gvs[] >>
  qx_gen_tac `i` >> strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[EL_CONS, PRE_SUB1] >> decide_tac
QED

Theorem gas_stack_ok_push_transfer:
  gas_stack_ok s /\ s.contexts = old::rest /\
  s'.contexts = child::parent::rest' /\ MAP FST rest' = MAP FST rest /\
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts) /\
  frame_unused_gas (FST child) <= (FST parent).gasUsed ==>
  gas_stack_ok s'
Proof
  simp[gas_stack_ok_def, unused_gas_def] >> strip_tac >> gvs[] >>
  qx_gen_tac `i` >> Cases_on `i` >> simp[] >>
  strip_tac >>
  `LENGTH rest' = LENGTH rest` by metis_tac[LENGTH_MAP] >>
  `FST (EL n rest') = FST (EL n rest)` by metis_tac[EL_MAP] >>
  `MAP FST (TAKE n rest') = MAP FST (TAKE n rest)` by metis_tac[MAP_TAKE] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[EL_CONS, PRE_SUB1] >> decide_tac
QED

Theorem gas_stack_ok_same_tail_transfer:
  gas_stack_ok s /\ s.contexts <> [] /\ s'.contexts <> [] /\
  MAP FST (TL s'.contexts) = MAP FST (TL s.contexts) /\
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts) ==>
  gas_stack_ok s'
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[] >>
  Cases_on `s'.contexts` >> gvs[gas_stack_ok_def, unused_gas_def] >>
  qx_gen_tac `i` >> strip_tac >>
  `LENGTH t' = LENGTH t` by metis_tac[LENGTH_MAP] >>
  `FST (EL i t') = FST (EL i t)` by metis_tac[EL_MAP] >>
  `MAP FST (TAKE i t') = MAP FST (TAKE i t)` by metis_tac[MAP_TAKE] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[EL_CONS, PRE_SUB1] >> decide_tac
QED

Theorem step_pop_preserves_gas_stack_ok:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts < LENGTH s.contexts ⇒
  gas_stack_ok s'
Proof
  strip_tac >>
  `s.contexts <> [] /\ gas_stack_ok s` by gvs[wf_state_def] >>
  drule_all step_unused_gas_nonincrease >> strip_tac >>
  drule step_pop_structure >> (impl_tac >- gvs[wf_state_def]) >>
  disch_then (qx_choosel_then [`new_head`, `parent`, `rest`] strip_assume_tac) >>
  Cases_on `s.contexts` >> gvs[] >>
  irule gas_stack_ok_pop_transfer >>
  goal_assum $ drule_at (Pat `gas_stack_ok`) >>
  goal_assum $ drule_at (Pat `s.contexts = _`) >> simp[]
QED

Theorem step_preserves_gas_stack_ok:
  wf_state s ⇒ gas_stack_ok (SND (step s))
Proof
  strip_tac >> Cases_on `step s` >> simp[] >>
  rename1 `step s = (_,s')` >> rename1 `step s = (r,s')` >>
  `s.contexts <> [] /\ gas_stack_ok s /\ outputTo_consistent_stack s` by
    gvs[wf_state_def] >>
  drule_all step_unused_gas_nonincrease >> strip_tac >>
  Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (`outputTo_consistent s` by
        metis_tac[outputTo_consistent_stack_imp_consistent] >>
      drule_all step_same_frame >> strip_tac >>
      irule gas_stack_ok_same_tail_transfer >>
      (conj_tac >- (Cases_on `s.contexts` >> Cases_on `s'.contexts` >> gvs[])) >>
      qexists_tac `s` >>
      gvs[same_frame_rel_def] >> Cases_on `s.contexts` >> gvs[]) >>
  Cases_on `LENGTH s'.contexts > LENGTH s.contexts`
  >- (drule_all step_grow_parent_unused_gas_ok >> strip_tac >>
      drule step_push_structure >> simp[] >> strip_tac >>
      Cases_on `s.contexts` >> gvs[] >>
      Cases_on `s'.contexts` >> gvs[] >> Cases_on `t'` >> gvs[] >>
      irule gas_stack_ok_push_transfer >>
      qexistsl_tac [`h'`, `h`, `h''`, `t`, `t''`, `s`] >> simp[]) >>
  `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac >>
  metis_tac[step_pop_preserves_gas_stack_ok]
QED

Theorem step_preserves_wf_state:
  wf_state s ⇒ wf_state (SND (step s))
Proof
  mp_tac decreases_gas_cred_step
  \\ mp_tac preserves_wf_accounts_step
  \\ mp_tac (GEN_ALL limits_num_contexts_step)
  \\ rewrite_tac[decreases_gas_cred_def, preserves_wf_accounts_def,
                 limits_num_contexts_def]
  \\ rw[wf_state_def]
  >- ( first_x_assum(qspec_then`s`mp_tac) \\ rw[] )
  >- ( `1026 = SUC 1025` by simp[] \\ metis_tac[LESS_EQ_IFF_LESS_SUC])
  >- ( first_x_assum(qspec_then`s`mp_tac) \\ rw[])
  >- ( irule step_preserves_stack_room_ok \\ simp[] \\ gvs[wf_state_def])
  >- ( irule step_preserves_gas_stack_ok \\ simp[] \\ gvs[wf_state_def])
  >- ( irule step_preserves_outputTo_consistent_stack \\ simp[] \\ gvs[wf_state_def])
QED

