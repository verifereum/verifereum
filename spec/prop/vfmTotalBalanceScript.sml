(*
 * The total ether in an account map, and a bound on it that every EVM step
 * and every transaction respects.
 *
 * A step never raises the total of any map in all_accounts above a bound
 * they were all within: value transfers keep the total, SELFDESTRUCT can
 * only lower it, a call or create saves a snapshot of the live map, and a
 * reverting pop restores a snapshot that was already in all_accounts.
 * A transaction never raises the total of the world it runs in: the gas
 * refund and the fee it credits are at most the gas it charged up front.
 *)
Theory vfmTotalBalance
Ancestors
  arithmetic list rich_list pred_set combin pair words While
  vfmTypes vfmState vfmContext vfmExecution vfmExecutionProp
  vfmDecreasesGas vfmStaticCalls vfmAccountFrame
Libs
  BasicProvers

Definition total_balance_def:
  total_balance (accounts:evm_accounts) =
    SIGMA (λx. (lookup_account x accounts).balance) (UNIV:address set)
End

(* -------------------------------------------------------------------------
 * The total under updates of one account.
 * ------------------------------------------------------------------------- *)

Theorem lookup_balance_le_total_balance:
  (lookup_account x a).balance ≤ total_balance a
Proof
  rw[total_balance_def]
  \\ qspecl_then [`λx. (lookup_account x a).balance`, `UNIV`, `x`]
       mp_tac SUM_IMAGE_IN_LE
  \\ simp[]
QED

Theorem total_balance_update_account:
  total_balance (update_account x v a) + (lookup_account x a).balance =
  total_balance a + v.balance
Proof
  `∀b. total_balance b =
       (lookup_account x b).balance +
       SIGMA (λy. (lookup_account y b).balance) (UNIV DELETE x)`
    by (gen_tac
        \\ qspecl_then [`x`, `b`] assume_tac
             (GEN_ALL lookup_balance_le_total_balance)
        \\ fs[total_balance_def, SUM_IMAGE_DELETE])
  \\ pop_assum (fn th => once_rewrite_tac[th])
  \\ `SIGMA (λy. (lookup_account y (update_account x v a)).balance)
        (UNIV DELETE x) =
      SIGMA (λy. (lookup_account y a).balance) (UNIV DELETE x)`
    by (irule SUM_IMAGE_CONG
        \\ simp[lookup_account_def, update_account_def, APPLY_UPDATE_THM])
  \\ simp[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

Theorem total_balance_update_account_le:
  v.balance ≤ (lookup_account x a).balance ⇒
  total_balance (update_account x v a) ≤ total_balance a
Proof
  strip_tac
  \\ qspecl_then [`x`, `v`, `a`] mp_tac
       (GEN_ALL total_balance_update_account)
  \\ decide_tac
QED

Theorem total_balance_update_account_same:
  v.balance = (lookup_account x a).balance ⇒
  total_balance (update_account x v a) = total_balance a
Proof
  strip_tac
  \\ qspecl_then [`x`, `v`, `a`] mp_tac
       (GEN_ALL total_balance_update_account)
  \\ decide_tac
QED

Theorem total_balance_transfer_value:
  v ≤ (lookup_account x a).balance ⇒
  total_balance (transfer_value x y v a) = total_balance a
Proof
  rw[transfer_value_def]
  \\ qmatch_goalsub_abbrev_tac `update_account y r (update_account x d a)`
  \\ qspecl_then [`x`, `d`, `a`] mp_tac (GEN_ALL total_balance_update_account)
  \\ qspecl_then [`y`, `r`, `update_account x d a`] mp_tac
       (GEN_ALL total_balance_update_account)
  \\ `lookup_account y (update_account x d a) = lookup_account y a`
       by gvs[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
  \\ simp[Abbr`r`, Abbr`d`]
  \\ decide_tac
QED

Theorem total_balance_increment_nonce[simp]:
  total_balance (increment_nonce x a) = total_balance a
Proof
  rw[increment_nonce_def]
  \\ irule total_balance_update_account_same \\ simp[]
QED

Theorem total_balance_clear_storage[simp]:
  total_balance (clear_storage x a) = total_balance a
Proof
  rw[clear_storage_def]
  \\ irule total_balance_update_account_same \\ simp[]
QED

Theorem total_balance_process_deletions:
  ∀ds a. total_balance (process_deletions ds a) ≤ total_balance a
Proof
  Induct \\ rw[process_deletions_def]
  \\ irule LESS_EQ_TRANS
  \\ first_x_assum $ irule_at Any
  \\ irule total_balance_update_account_le
  \\ simp[empty_account_state_def]
QED

(* -------------------------------------------------------------------------
 * Every map in all_accounts within a bound, preserved by a computation.
 * ------------------------------------------------------------------------- *)

Definition balance_bounded_def:
  balance_bounded B s ⇔
    EVERY (λaccs. total_balance accs ≤ B) (all_accounts s)
End

(* From any state with a frame that satisfies P and is within B, m leaves
   a state within B. *)
Definition tb_pres_def:
  tb_pres B P (m: α execution) ⇔
    ∀s. s.contexts ≠ [] ∧ P s ∧ balance_bounded B s ⇒
        balance_bounded B (SND (m s))
End

Theorem tb_pres_mono:
  tb_pres B P m ∧ (∀s. Q s ⇒ P s) ⇒ tb_pres B Q m
Proof
  rw[tb_pres_def]
QED

Theorem tb_pres_any:
  tb_pres B (K T) m ⇒ tb_pres B P m
Proof
  rw[tb_pres_def]
QED

Theorem tb_pres_bind:
  tb_pres B P g ∧ (∀x. tb_pres B (Q x) (f x)) ∧
  (∀s x t. s.contexts ≠ [] ∧ P s ∧ balance_bounded B s ∧
           g s = (INL x, t) ⇒ t.contexts ≠ [] ∧ Q x t) ⇒
  tb_pres B P (bind g f)
Proof
  rw[tb_pres_def, bind_def]
  \\ Cases_on `g s`
  \\ `balance_bounded B r` by metis_tac[SND]
  \\ Cases_on `q` \\ gvs[]
  \\ metis_tac[]
QED

Theorem tb_pres_ignore_bind:
  tb_pres B P g ∧ tb_pres B Q f ∧
  (∀s x t. s.contexts ≠ [] ∧ P s ∧ balance_bounded B s ∧
           g s = (INL x, t) ⇒ t.contexts ≠ [] ∧ Q t) ⇒
  tb_pres B P (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  \\ irule tb_pres_bind \\ simp[]
  \\ qexists_tac `K Q` \\ simp[]
  \\ metis_tac[]
QED

Theorem tb_pres_ignore_bind_K:
  tb_pres B P g ∧ tb_pres B (K T) f ∧
  (∀s x t. s.contexts ≠ [] ∧ P s ∧ balance_bounded B s ∧
           g s = (INL x, t) ⇒ t.contexts ≠ []) ⇒
  tb_pres B P (ignore_bind g f)
Proof
  rw[] \\ irule tb_pres_ignore_bind \\ simp[]
  \\ qexists_tac `K T` \\ simp[] \\ metis_tac[]
QED

Theorem tb_pres_handle:
  tb_pres B P f ∧ (∀e. tb_pres B (Q e) (h e)) ∧
  (∀s e t. s.contexts ≠ [] ∧ P s ∧ balance_bounded B s ∧
           f s = (INR e, t) ⇒ t.contexts ≠ [] ∧ Q e t) ⇒
  tb_pres B P (handle f h)
Proof
  rw[tb_pres_def, handle_def]
  \\ Cases_on `f s`
  \\ `balance_bounded B r` by metis_tac[SND]
  \\ Cases_on `q` \\ gvs[]
  \\ metis_tac[]
QED

Theorem cp_all_accounts:
  cp m ∧ m s = (r, t) ∧ s.contexts ≠ [] ⇒
  cp_rel s t ∧ t.contexts ≠ [] ∧ all_accounts t = all_accounts s
Proof
  strip_tac
  \\ `cp_rel s t` by (gvs[cp_def, cp_rel_def] \\ metis_tac[])
  \\ gvs[cp_rel_def, all_accounts_def]
  \\ Cases_on `s.contexts` \\ gvs[]
QED

Theorem tb_pres_cp:
  cp m ⇒ tb_pres B P m
Proof
  rw[tb_pres_def, balance_bounded_def]
  \\ Cases_on `m s`
  \\ drule_all cp_all_accounts \\ simp[]
QED

(* A cp step keeps every precondition closed under cp_rel. *)
Theorem tb_pres_bind_cp:
  cp g ∧ (∀x. tb_pres B P (f x)) ∧
  (∀s t. s.contexts ≠ [] ∧ P s ∧ cp_rel s t ⇒ P t) ⇒
  tb_pres B P (bind g f)
Proof
  strip_tac
  \\ irule tb_pres_bind \\ simp[tb_pres_cp]
  \\ qexists_tac `K P` \\ simp[]
  \\ rpt gen_tac \\ strip_tac
  \\ drule_all cp_all_accounts \\ metis_tac[]
QED

Theorem tb_pres_ignore_bind_cp:
  cp g ∧ tb_pres B P f ∧
  (∀s t. s.contexts ≠ [] ∧ P s ∧ cp_rel s t ⇒ P t) ⇒
  tb_pres B P (ignore_bind g f)
Proof
  rw[ignore_bind_def] \\ irule tb_pres_bind_cp \\ simp[] \\ metis_tac[]
QED

Theorem tb_pres_bind_get_accounts:
  (∀x. tb_pres B (λs. P s ∧ s.rollback.accounts = x) (f x)) ⇒
  tb_pres B P (bind get_accounts f)
Proof
  rw[tb_pres_def, bind_def, get_accounts_def, return_def]
QED

Theorem tb_pres_bind_get_rollback:
  (∀x. tb_pres B (λs. P s ∧ total_balance x.accounts ≤ B) (f x)) ⇒
  tb_pres B P (bind get_rollback f)
Proof
  rw[tb_pres_def, bind_def, get_rollback_def, return_def]
  \\ first_x_assum irule
  \\ gvs[balance_bounded_def, all_accounts_def]
QED

Theorem tb_pres_bind_get_num_contexts:
  (∀n. tb_pres B (λs. P s ∧ LENGTH s.contexts = n) (f n)) ⇒
  tb_pres B P (bind get_num_contexts f)
Proof
  rw[tb_pres_def, bind_def, get_num_contexts_def, return_def]
QED

(* -------------------------------------------------------------------------
 * Leaves that change the accounts or the context stack.
 * ------------------------------------------------------------------------- *)

Theorem tb_pres_update_accounts:
  (∀s. s.contexts ≠ [] ∧ P s ⇒
       total_balance (f s.rollback.accounts) ≤ total_balance s.rollback.accounts) ⇒
  tb_pres B P (update_accounts f)
Proof
  rw[tb_pres_def, update_accounts_def, return_def, balance_bounded_def,
     all_accounts_def]
  \\ first_x_assum drule_all \\ decide_tac
QED

Theorem tb_pres_set_current_context:
  tb_pres B P (set_current_context c)
Proof
  rw[tb_pres_def, set_current_context_def, return_def, fail_def,
     balance_bounded_def, all_accounts_def]
  \\ Cases_on `s.contexts` \\ gvs[]
QED

Theorem tb_pres_push_logs:
  tb_pres B P (push_logs ls)
Proof
  irule tb_pres_any \\ rw[push_logs_def]
  \\ irule tb_pres_bind_cp \\ simp[tb_pres_set_current_context]
QED

Theorem tb_pres_set_tStorage:
  tb_pres B P (set_tStorage x)
Proof
  rw[tb_pres_def, set_tStorage_def, return_def, balance_bounded_def,
     all_accounts_def]
QED

Theorem tb_pres_set_original:
  tb_pres B P (set_original x)
Proof
  rw[tb_pres_def, set_original_def, return_def, fail_def,
     balance_bounded_def, all_accounts_def]
QED

Theorem tb_pres_add_to_delete:
  tb_pres B P (add_to_delete x)
Proof
  rw[tb_pres_def, add_to_delete_def, return_def,
     balance_bounded_def, all_accounts_def]
QED

Theorem tb_pres_push_context:
  tb_pres B (λs. total_balance (SND crb).accounts ≤ B) (push_context crb)
Proof
  rw[tb_pres_def, push_context_def, return_def,
     balance_bounded_def, all_accounts_def]
  \\ Cases_on `s.contexts` \\ gvs[FRONT_DEF]
QED

Theorem tb_pres_pop_and_incorporate_context:
  tb_pres B (λs. 2 ≤ LENGTH s.contexts) (pop_and_incorporate_context b)
Proof
  rw[tb_pres_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ Cases_on `t` \\ gvs[]
  \\ PairCases_on `h` \\ PairCases_on `h'`
  \\ Cases_on `b` \\ Cases_on `t'`
  \\ gvs[pop_and_incorporate_context_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, pop_context_def,
         unuse_gas_def, set_current_context_def, assert_def,
         return_def, fail_def, push_logs_def, update_gas_refund_def,
         set_rollback_def, balance_bounded_def, all_accounts_def, FRONT_DEF]
  \\ rw[] \\ gvs[] \\ Cases_on `t` \\ gvs[FRONT_DEF]
QED

(* -------------------------------------------------------------------------
 * The instructions.
 * ------------------------------------------------------------------------- *)

val cp_rel_tac =
  rw[cp_rel_def] \\ gvs[] \\ Cases_on `s.contexts` \\ gvs[];

val cp_solve_tac =
  (simp[] \\ NO_TAC) ORELSE (rpt CASE_TAC \\ simp[] \\ NO_TAC);

(* Peel one bind or ignore_bind off the goal: a getter whose value the rest
   needs, or a cp step. *)
val tb_peel_tac =
  (irule tb_pres_bind_get_accounts ORELSE
   irule tb_pres_bind_get_rollback ORELSE
   irule tb_pres_bind_get_num_contexts ORELSE
   ((ho_match_mp_tac tb_pres_bind_cp ORELSE
     ho_match_mp_tac tb_pres_ignore_bind_cp)
    \\ conj_tac >- cp_solve_tac
    \\ reverse conj_tac >- cp_rel_tac))
  \\ TRY gen_tac \\ simp[];

val tb_peel = rpt tb_peel_tac;

val ctx_tac =
  rw[] \\ gvs[update_accounts_def, add_to_delete_def, push_context_def,
              set_original_def, ignore_bind_def, bind_def, return_def,
              fail_def, AllCaseEqs()];

Theorem tb_pres_step_sstore:
  tb_pres B P (step_sstore t)
Proof
  irule tb_pres_any
  \\ simp[step_sstore_def] \\ tb_peel
  \\ Cases_on `t` \\ simp[]
  >- (simp[write_transient_storage_def] \\ tb_peel
      \\ simp[tb_pres_set_tStorage])
  \\ simp[write_storage_def]
  \\ irule tb_pres_update_accounts \\ rw[]
  \\ irule (iffRL LESS_OR_EQ) \\ disj2_tac
  \\ irule total_balance_update_account_same \\ simp[]
QED

Theorem tb_pres_step_log:
  tb_pres B P (step_log n)
Proof
  irule tb_pres_any
  \\ simp[step_log_def] \\ tb_peel
  \\ simp[tb_pres_push_logs]
QED

Theorem tb_pres_step_self_destruct:
  tb_pres B P step_self_destruct
Proof
  irule tb_pres_any
  \\ simp[step_self_destruct_def] \\ tb_peel
  \\ ho_match_mp_tac tb_pres_ignore_bind_K \\ rpt conj_tac
  >- (irule tb_pres_update_accounts \\ rw[]
      \\ irule (iffRL LESS_OR_EQ) \\ disj2_tac
      \\ irule total_balance_transfer_value \\ simp[])
  >- (tb_peel
      \\ ho_match_mp_tac tb_pres_ignore_bind_K \\ rpt conj_tac
      >- (IF_CASES_TAC \\ simp[tb_pres_cp]
          \\ ho_match_mp_tac tb_pres_ignore_bind_K \\ rpt conj_tac
          >- (irule tb_pres_update_accounts \\ rw[]
              \\ irule total_balance_update_account_le \\ simp[])
          >- simp[tb_pres_add_to_delete]
          \\ ctx_tac)
      >- simp[tb_pres_cp]
      \\ ctx_tac)
  \\ ctx_tac
QED

Theorem tb_pres_proceed_call:
  tb_pres B (λs. value ≤ (lookup_account sender s.rollback.accounts).balance)
    (proceed_call op sender address value ao az code stipend rd)
Proof
  simp[proceed_call_def] \\ tb_peel
  \\ ho_match_mp_tac (GEN_ALL tb_pres_ignore_bind)
  \\ qexists_tac `λs. total_balance x.accounts ≤ B` \\ simp[]
  \\ rpt conj_tac
  >- (IF_CASES_TAC \\ simp[tb_pres_cp]
      \\ irule tb_pres_update_accounts \\ rw[]
      \\ irule (iffRL LESS_OR_EQ) \\ disj2_tac
      \\ irule total_balance_transfer_value \\ simp[])
  >- (tb_peel
      \\ ho_match_mp_tac (GEN_ALL tb_pres_ignore_bind)
      \\ qexists_tac `K T` \\ simp[]
      \\ rpt conj_tac
      >- (irule tb_pres_mono \\ irule_at Any tb_pres_push_context \\ simp[])
      >- (IF_CASES_TAC \\ simp[tb_pres_cp])
      \\ ctx_tac)
  \\ ctx_tac
QED

Theorem tb_pres_step_call:
  tb_pres B P (step_call op)
Proof
  irule tb_pres_any
  \\ simp[step_call_def] \\ tb_peel
  \\ rpt (pairarg_tac \\ simp[] \\ tb_peel)
  \\ IF_CASES_TAC \\ simp[tb_pres_cp]
  \\ tb_peel
  \\ IF_CASES_TAC \\ simp[tb_pres_cp]
  \\ irule tb_pres_mono
  \\ irule_at Any tb_pres_proceed_call
  \\ rw[] \\ gvs[NOT_LESS]
QED

Theorem tb_pres_proceed_create:
  tb_pres B (λs. value ≤ (lookup_account sender s.rollback.accounts).balance)
    (proceed_create sender address value code gas)
Proof
  simp[proceed_create_def]
  \\ ho_match_mp_tac (GEN_ALL tb_pres_ignore_bind)
  \\ qexists_tac `λs. value ≤ (lookup_account sender s.rollback.accounts).balance`
  \\ simp[]
  \\ rpt conj_tac
  >- (irule tb_pres_update_accounts \\ simp[])
  >- (tb_peel
      \\ ho_match_mp_tac (GEN_ALL tb_pres_ignore_bind)
      \\ qexists_tac `λs. value ≤ (lookup_account sender s.rollback.accounts).balance ∧
                          total_balance x.accounts ≤ B`
      \\ simp[tb_pres_set_original]
      \\ conj_tac
      >- (ho_match_mp_tac (GEN_ALL tb_pres_ignore_bind)
          \\ qexists_tac `λs. total_balance x.accounts ≤ B`
          \\ simp[]
          \\ rpt conj_tac
          >- (irule tb_pres_update_accounts \\ rw[]
              \\ irule (iffRL LESS_OR_EQ) \\ disj2_tac
              \\ qmatch_goalsub_abbrev_tac `transfer_value _ _ _ a'`
              \\ `total_balance a' = total_balance s.rollback.accounts`
                   by simp[Abbr`a'`]
              \\ pop_assum (SUBST1_TAC o SYM)
              \\ irule total_balance_transfer_value
              \\ simp[Abbr`a'`, clear_storage_nonce_code_balance])
          >- (irule tb_pres_mono \\ irule_at Any tb_pres_push_context \\ simp[])
          \\ ctx_tac)
      \\ ctx_tac)
  \\ ctx_tac
QED

Theorem tb_pres_step_create:
  tb_pres B P (step_create two)
Proof
  irule tb_pres_any
  \\ simp[step_create_def] \\ tb_peel
  \\ IF_CASES_TAC \\ simp[tb_pres_cp]
  \\ tb_peel
  \\ IF_CASES_TAC
  >- (simp[abort_create_exists_def]
      \\ ho_match_mp_tac (GEN_ALL tb_pres_ignore_bind)
      \\ qexists_tac `K T` \\ simp[tb_pres_cp]
      \\ conj_tac
      >- (irule tb_pres_update_accounts \\ simp[])
      \\ ctx_tac)
  \\ irule tb_pres_mono
  \\ irule_at Any tb_pres_proceed_create
  \\ rw[] \\ gvs[NOT_LESS]
QED

Theorem tb_pres_step_inst:
  tb_pres B P (step_inst op)
Proof
  Cases_on `op`
  \\ simp[tb_pres_cp, cp_step_inst_non_call]
  \\ simp[step_inst_def, tb_pres_step_sstore, tb_pres_step_log,
          tb_pres_step_self_destruct, tb_pres_step_call,
          tb_pres_step_create]
QED

(* -------------------------------------------------------------------------
 * The handlers and the step.
 * ------------------------------------------------------------------------- *)

Theorem tb_pres_handle_create:
  tb_pres B P (handle_create e)
Proof
  irule tb_pres_any
  \\ simp[handle_create_def] \\ tb_peel
  \\ rpt CASE_TAC \\ simp[tb_pres_cp]
  \\ tb_peel
  \\ ho_match_mp_tac tb_pres_ignore_bind_K \\ rpt conj_tac
  \\ TRY (irule tb_pres_update_accounts \\ rw[]
           \\ irule (iffRL LESS_OR_EQ) \\ disj2_tac
           \\ irule total_balance_update_account_same
           \\ simp[] \\ NO_TAC)
  \\ TRY (simp[tb_pres_cp] \\ NO_TAC)
  \\ ctx_tac
QED

Theorem tb_pres_handle_ex_helper:
  tb_pres B P (handle_ex_helper e)
Proof
  irule tb_pres_any
  \\ simp[handle_ex_helper_def] \\ tb_peel
  \\ IF_CASES_TAC \\ simp[tb_pres_cp]
  \\ tb_peel
  \\ ho_match_mp_tac (GEN_ALL tb_pres_ignore_bind)
  \\ qexists_tac `K T` \\ simp[tb_pres_cp]
  \\ conj_tac
  >- (irule tb_pres_mono
      \\ irule_at Any tb_pres_pop_and_incorporate_context
      \\ simp[])
  \\ rpt strip_tac
  \\ `LENGTH s.contexts > 1` by simp[]
  \\ drule pop_and_incorporate_context_preserves
  \\ disch_then (qspec_then `e = NONE` mp_tac) \\ simp[]
QED

Theorem tb_pres_handle_exception:
  tb_pres B P (handle_exception e)
Proof
  irule tb_pres_any
  \\ `handle_exception e =
      bind (if e ≠ NONE ∧ e ≠ SOME Reverted then
              do gasLeft <- get_gas_left; consume_gas gasLeft;
                 set_return_data [] od
            else return ())
           (λu. handle_ex_helper e)`
       by simp[FUN_EQ_THM, handle_exception_decomp]
  \\ pop_assum SUBST1_TAC
  \\ irule tb_pres_bind_cp \\ simp[tb_pres_handle_ex_helper]
  \\ rw[]
QED

Theorem tb_pres_handle_step:
  tb_pres B P (handle_step e)
Proof
  rw[handle_step_def] \\ simp[tb_pres_cp]
  \\ ho_match_mp_tac (GEN_ALL tb_pres_handle)
  \\ qexists_tac `K (K T)`
  \\ simp[tb_pres_handle_create, tb_pres_handle_exception]
  \\ metis_tac[handle_create_preserves_nonempty_contexts, SND]
QED

Theorem tb_pres_step:
  tb_pres B P step
Proof
  irule tb_pres_any
  \\ simp[step_def]
  \\ ho_match_mp_tac (GEN_ALL tb_pres_handle)
  \\ qexists_tac `K (K T)`
  \\ simp[tb_pres_handle_step]
  \\ conj_tac
  >- (tb_peel
      \\ Cases_on `FLOOKUP context'.msgParams.parsed context'.pc` \\ simp[]
      >- (IF_CASES_TAC \\ simp[tb_pres_step_inst])
      \\ ho_match_mp_tac tb_pres_ignore_bind_K
      \\ simp[tb_pres_step_inst, tb_pres_cp]
      \\ metis_tac[step_inst_preserves_nonempty_contexts, SND])
  \\ rw[bind_def, ignore_bind_def, get_current_context_def, return_def,
        fail_def]
  \\ gvs[AllCaseEqs()]
  \\ qpat_x_assum `_ s = (INR _,_)` mp_tac
  \\ Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
                       (FST (HD s.contexts)).pc` \\ simp[]
  >- (IF_CASES_TAC \\ rw[]
      \\ metis_tac[step_inst_preserves_nonempty_contexts, SND])
  \\ simp[bind_def] \\ Cases_on `step_inst x s` \\ Cases_on `q` \\ rw[]
  \\ metis_tac[step_inst_preserves_nonempty_contexts,
               inc_pc_or_jump_preserves_nonempty_contexts, SND]
QED

Theorem step_total_balance_bounded:
  wf_state s ∧ EVERY (λaccs. total_balance accs ≤ B) (all_accounts s) ⇒
  EVERY (λaccs. total_balance accs ≤ B) (all_accounts (SND (step s)))
Proof
  strip_tac
  \\ mp_tac (Q.INST [`P` |-> `K T`] tb_pres_step)
  \\ simp[tb_pres_def, balance_bounded_def]
  \\ disch_then irule \\ gvs[wf_state_def]
QED

(* -------------------------------------------------------------------------
 * A transaction.
 * ------------------------------------------------------------------------- *)

Theorem balance_bounded_rollback:
  balance_bounded B s ⇒ total_balance s.rollback.accounts ≤ B
Proof
  rw[balance_bounded_def, all_accounts_def]
QED

Theorem balance_bounded_one_context:
  LENGTH s.contexts = 1 ⇒
  (balance_bounded B s ⇔ total_balance s.rollback.accounts ≤ B)
Proof
  Cases_on `s.contexts` \\ rw[balance_bounded_def, all_accounts_def]
  \\ gvs[LENGTH_EQ_NUM_compute, FRONT_DEF]
QED

Theorem run_balance_bounded:
  run s = SOME (r, t) ∧ s.contexts ≠ [] ∧ balance_bounded B s ⇒
  balance_bounded B t
Proof
  qsuff_tac
    `∀p q. OWHILE (ISL o FST) (step o SND) p = SOME q ⇒
           (SND p).contexts ≠ [] ∧ balance_bounded B (SND p) ⇒
           balance_bounded B (SND q)`
  >- (rw[run_def] \\ first_x_assum drule \\ simp[])
  \\ ho_match_mp_tac OWHILE_IND \\ rw[]
  \\ first_x_assum irule
  \\ simp[step_preserves_nonempty_contexts]
  \\ mp_tac (Q.INST [`P` |-> `K T`] tb_pres_step)
  \\ simp[tb_pres_def]
QED

Theorem tb_pres_precompile:
  tb_pres B P (handle (dispatch_precompiles a) handle_step)
Proof
  ho_match_mp_tac (GEN_ALL tb_pres_handle)
  \\ qexists_tac `K (K T)`
  \\ simp[tb_pres_cp, tb_pres_handle_step]
  \\ rpt strip_tac
  \\ drule_all (REWRITE_RULE [cp_def] cp_dispatch_precompiles)
  \\ rw[] \\ gvs[]
QED

Theorem precompile_balance_bounded:
  handle (dispatch_precompiles a) handle_step s = (r, t) ∧
  s.contexts ≠ [] ∧ balance_bounded B s ⇒
  balance_bounded B t
Proof
  strip_tac
  \\ mp_tac (Q.INST [`P` |-> `K T`] tb_pres_precompile)
  \\ rw[tb_pres_def] \\ first_x_assum drule \\ gvs[]
QED

Theorem total_balance_pre_transaction_updates:
  pre_transaction_updates a bbf t = SOME a' ⇒
  total_balance a' + t.gasLimit * t.gasPrice ≤ total_balance a ∧
  t.value ≤ (lookup_account t.from a').balance ∧
  calldata_floor_cost t.data ≤ t.gasLimit
Proof
  strip_tac \\ gvs[pre_transaction_updates_def, AllCaseEqs()]
  \\ qmatch_goalsub_abbrev_tac `update_account t.from v a`
  \\ qspecl_then [`t.from`, `v`, `a`] mp_tac
       (GEN_ALL total_balance_update_account)
  \\ qabbrev_tac `f1 = t.gasLimit * t.gasPrice`
  \\ qabbrev_tac `f2 = total_blob_gas t * bbf`
  \\ gvs[Abbr`v`, lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

Theorem lookup_balance_process_authorization:
  process_authorization c au (a, x, r) = (a', x', r') ⇒
  (lookup_account y a').balance = (lookup_account y a).balance
Proof
  rw[process_authorization_def]
  \\ gvs[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
  \\ rw[]
QED

Theorem lookup_balance_process_authorizations:
  ∀auths a x r a' x' r'.
    process_authorizations c auths a x r = (a', x', r') ⇒
    ∀y. (lookup_account y a').balance = (lookup_account y a).balance
Proof
  Induct \\ rw[process_authorizations_def]
  \\ pairarg_tac \\ gvs[]
  \\ first_x_assum drule \\ rw[]
  \\ drule lookup_balance_process_authorization \\ simp[]
QED

Theorem initial_state_total_balance:
  initial_state dom static chainId prevHashes blk accs tx = SOME s ⇒
  total_balance s.rollback.accounts + tx.gasLimit * tx.gasPrice ≤
    total_balance accs ∧
  tx.value ≤ (lookup_account tx.from s.rollback.accounts).balance ∧
  calldata_floor_cost tx.data ≤ tx.gasLimit ∧
  LENGTH s.contexts = 1 ∧ s.contexts ≠ []
Proof
  strip_tac \\ gvs[initial_state_def, AllCaseEqs(), initial_rollback_def]
  \\ rpt (pairarg_tac \\ gvs[])
  \\ drule total_balance_pre_transaction_updates \\ strip_tac
  \\ drule lookup_balance_process_authorizations \\ strip_tac
  \\ `total_balance postAuthAccounts = total_balance accounts`
       by simp[total_balance_def]
  \\ gvs[AllCaseEqs()]
QED

Theorem transaction_gas_accounting_le:
  transaction_gas_accounting gp bf gL floor (gl, sr, ar) = (tu, re, tf) ∧
  floor ≤ gL ⇒
  re + tf ≤ gL * gp
Proof
  strip_tac
  \\ qpat_x_assum `transaction_gas_accounting _ _ _ _ _ = _` mp_tac
  \\ simp_tac std_ss [transaction_gas_accounting_def, LET_THM, PAIR_EQ]
  \\ strip_tac
  \\ `tu ≤ gL`
       by (qpat_x_assum `MAX _ _ = tu` (SUBST1_TAC o SYM) \\ simp[MAX_LE])
  \\ `tf ≤ tu * gp`
       by (qpat_x_assum `_ = tf` (SUBST1_TAC o SYM) \\ simp[])
  \\ `re + tu * gp = gL * gp`
       by (qpat_x_assum `_ = re` (SUBST1_TAC o SYM)
           \\ simp[GSYM RIGHT_ADD_DISTRIB])
  \\ qabbrev_tac `X = tu * gp` \\ qabbrev_tac `Y = gL * gp`
  \\ qpat_x_assum `tf ≤ X` mp_tac \\ qpat_x_assum `re + X = Y` mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ decide_tac
QED

Theorem total_balance_add_balance:
  total_balance
    (update_account x (lookup_account x a with balance updated_by $+ n) a) =
  total_balance a + n
Proof
  qspecl_then [`x`, `lookup_account x a with balance updated_by $+ n`, `a`]
    mp_tac (GEN_ALL total_balance_update_account)
  \\ simp[]
QED

Theorem total_balance_post_transaction_accounting:
  post_transaction_accounting blk tx result acc t = (r, a') ∧
  calldata_floor_cost tx.data ≤ tx.gasLimit ∧
  total_balance acc ≤ B ∧ total_balance t.rollback.accounts ≤ B ⇒
  total_balance a' ≤ B + tx.gasLimit * tx.gasPrice
Proof
  strip_tac \\ gvs[post_transaction_accounting_def]
  \\ rpt (pairarg_tac \\ gvs[])
  \\ drule_all transaction_gas_accounting_le \\ strip_tac
  \\ qabbrev_tac `fee = tx.gasLimit * tx.gasPrice`
  \\ Cases_on `result` \\ gvs[total_balance_add_balance]
  \\ irule LESS_EQ_TRANS \\ irule_at Any total_balance_process_deletions
  \\ simp[total_balance_add_balance]
QED

Theorem post_transaction_accounting_le:
  post_transaction_accounting blk tx r0 acc t = (r, a') ⇒
  calldata_floor_cost tx.data ≤ tx.gasLimit ∧
  total_balance acc + tx.gasLimit * tx.gasPrice ≤ total_balance A ∧
  total_balance t.rollback.accounts ≤ total_balance acc ⇒
  total_balance a' ≤ total_balance A
Proof
  rpt strip_tac
  \\ drule total_balance_post_transaction_accounting
  \\ disch_then (qspec_then `total_balance acc` mp_tac) \\ simp[]
  \\ qabbrev_tac `fee = tx.gasLimit * tx.gasPrice`
  \\ decide_tac
QED

Theorem run_transaction_total_balance:
  run_transaction dom static chainId prevHashes blk accounts tx =
    SOME (r, accounts') ⇒
  total_balance accounts' ≤ total_balance accounts
Proof
  strip_tac \\ gvs[run_transaction_def, run_create_def, AllCaseEqs()]
  \\ drule initial_state_total_balance \\ strip_tac
  \\ drule post_transaction_accounting_le \\ disch_then irule \\ simp[]
  \\ irule balance_bounded_rollback
  >~ [`handle (dispatch_precompiles _) handle_step _ = _`]
  >- (drule precompile_balance_bounded \\ disch_then irule
      \\ gvs[balance_bounded_one_context, total_balance_transfer_value])
  \\ drule run_balance_bounded \\ disch_then irule
  \\ gvs[balance_bounded_one_context, total_balance_transfer_value]
QED
