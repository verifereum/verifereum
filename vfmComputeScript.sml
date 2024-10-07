open HolKernel boolLib bossLib Parse dep_rewrite blastLib
     cv_typeTheory cv_transLib cv_typeLib
     cvTheory cv_stdTheory
     pairTheory combinTheory wordsTheory alistTheory arithmeticTheory
     sptreeTheory vfmContextTheory vfmStateTheory vfmExecutionTheory;

val _ = new_theory "vfmCompute";

open finite_setTheory pred_setTheory

Theorem wf_list_to_num_set:
  !ls. wf (list_to_num_set ls)
Proof
  Induct \\ rw[list_to_num_set_def, wf_insert]
QED

Theorem MEM_fset_REP:
  MEM x (fset_REP fs) <=> fIN x fs
Proof
  rw[fIN_def]
QED

val from_to_num_set = from_to_thm_for “:num_set”;
val to_num_set = from_to_num_set |> concl |> rand;
val from_num_set = from_to_num_set |> concl |> rator |> rand;

Definition to_num_fset_def:
  to_num_fset cv = fromSet (domain (^to_num_set cv))
End

Definition from_num_fset_def:
  from_num_fset fs = ^from_num_set $ list_to_num_set $ fset_REP fs
End

Theorem from_to_num_fset[cv_from_to]:
  from_to from_num_fset to_num_fset
Proof
  rw[from_to_def, from_num_fset_def, to_num_fset_def]
  \\ rw[GSYM toSet_11, toSet_fromSet]
  \\ mp_tac from_to_num_set
  \\ gs[from_to_def, EXTENSION, GSYM fIN_IN, domain_list_to_num_set, fIN_def]
QED

Theorem fINSERT_num_cv_rep[cv_rep]:
  from_num_fset (fINSERT e s) =
  cv_insert (Num e) (from_unit ()) (from_num_fset s)
Proof
  rw[from_num_fset_def, GSYM cv_insert_thm]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ rw[wf_insert, wf_list_to_num_set,
        lookup_list_to_num_set, lookup_insert,
        MEM_fset_REP]
  \\ gs[]
QED

Theorem fIN_num_cv_rep[cv_rep]:
  b2c (fIN e s) =
  cv_ispair $ (cv_lookup (Num e) (from_num_fset s))
Proof
  rw[from_num_fset_def, GSYM cv_lookup_thm, from_option_def,
     lookup_list_to_num_set, MEM_fset_REP]
QED

(* -- *)

val from_to_bytes32 = from_to_thm_for “:bytes32”;

val to_bytes32 = from_to_bytes32 |> concl |> rand;
val from_bytes32 = from_to_bytes32 |> concl |> rator |> rand;

Definition to_storage_def:
  to_storage cv : storage =
  let t = to_sptree_spt ^to_bytes32 cv in
    FOLDR (λ(k,v) f. (n2w k =+ v) f) (λk. 0w) (toSortedAList t)
End

Definition build_spt_def:
  build_spt z 0 m = LN ∧
  build_spt z (SUC n) m =
    if m (n2w n) = z then build_spt z n m
    else insert n (m (n2w n)) (build_spt z n m)
End

Theorem wf_build_spt[simp]:
  ∀n m. wf (build_spt z n m)
Proof
  Induct \\ gvs[build_spt_def] \\ rw[wf_insert]
QED

Theorem lookup_build_spt:
  ∀n k. lookup k (build_spt z n m) =
  if n ≤ k then NONE
  else if m (n2w k) = z then NONE
  else SOME (m (n2w k))
Proof
  Induct \\ gvs[build_spt_def]
  \\ rw[lookup_insert, LESS_OR_EQ]
  \\ gvs[NOT_LESS] \\ rw[] \\ gvs[]
  \\ strip_tac \\ gvs[]
QED

Theorem build_spt_empty_storage[simp]:
  ∀n. build_spt 0w n empty_storage = LN
Proof
  Induct \\ gvs[build_spt_def, empty_storage_def]
QED

Definition from_storage_def:
  from_storage (s: storage) =
  from_sptree_sptree_spt ^from_bytes32 (build_spt 0w (dimword (:256)) s)
End

val from_to_storage_spt = from_to_thm_for “:bytes32 num_map”;

Theorem FOLDR_UPDATE_lookup:
  ∀gi ls t.
    (∀k. ALOOKUP ls k = lookup k t) ∧
    ALL_DISTINCT (MAP FST ls) ∧
    (∀x. x ∈ domain t ⇒ gi (g x) = x) ∧
    (∀x. g (gi x) = x)
  ⇒
  FOLDR (λ(k,v) f. (g k =+ v) f) (λk. a) ls =
  (λk. case lookup (gi k) t of NONE => a | SOME v => v)
Proof
  gen_tac \\ Induct \\ gvs[FORALL_PROD, FUN_EQ_THM]
  \\ rw[ APPLY_UPDATE_THM]
  \\ rw[] \\ gvs[]
  >- (
    qmatch_goalsub_rename_tac`g1 (g k)`
    \\ qmatch_goalsub_rename_tac`v = _`
    \\ `lookup k t = SOME v` by metis_tac[]
    \\ `k ∈ domain t` by metis_tac[domain_lookup]
    \\ simp[] )
  \\ qmatch_assum_rename_tac`g q ≠ k`
  \\ qmatch_asmsub_rename_tac`COND _ (SOME v)`
  \\ `lookup q t = SOME v` by metis_tac[]
  \\ `q ∈ domain t` by metis_tac[domain_lookup]
  \\ first_x_assum(qspec_then`delete q t`mp_tac)
  \\ gvs[lookup_delete]
  \\ impl_tac
  >- ( rw[] \\ metis_tac[ALOOKUP_NONE] )
  \\ rw[]
  \\ metis_tac[]
QED

Theorem from_to_storage[cv_from_to]:
  from_to from_storage to_storage
Proof
  rewrite_tac[from_to_def, from_storage_def, to_storage_def]
  \\ rw[from_to_storage_spt |> REWRITE_RULE[from_to_def]]
  \\ qmatch_goalsub_abbrev_tac`toSortedAList t`
  \\ DEP_REWRITE_TAC[Q.ISPEC`w2n`FOLDR_UPDATE_lookup]
  \\ simp[ALL_DISTINCT_MAP_FST_toSortedAList, ALOOKUP_toSortedAList]
  \\ simp[Abbr`t`, lookup_build_spt, domain_lookup, FUN_EQ_THM]
  \\ rw[]
  \\ qspec_then`k`mp_tac w2n_lt
  \\ gs[]
QED

Theorem empty_storage_cv_rep[cv_rep]:
  from_storage empty_storage = Num 0
Proof
  rw[from_storage_def] \\ EVAL_TAC
QED

val from_to_account_state = from_to_thm_for “:account_state”;
val to_account_state = from_to_account_state |> concl |> rand;
val from_account_state = from_to_account_state |> concl |> rator |> rand;

Definition to_evm_accounts_def:
  to_evm_accounts cv : evm_accounts =
  let t = to_sptree_spt ^to_account_state cv in
    FOLDR (λ(k,v) f. (n2w k =+ v) f) (λk. empty_account_state) (toSortedAList t)
End

Definition from_evm_accounts_def:
  from_evm_accounts (a: evm_accounts) =
  from_sptree_sptree_spt ^from_account_state
    (build_spt empty_account_state (dimword (:160)) a)
End

val from_to_evm_accounts_spt = from_to_thm_for “:account_state num_map”;

Theorem from_to_evm_accounts[cv_from_to]:
  from_to from_evm_accounts to_evm_accounts
Proof
  rw[from_to_def, from_evm_accounts_def, to_evm_accounts_def]
  \\ rw[from_to_evm_accounts_spt |> REWRITE_RULE[from_to_def]]
  \\ qmatch_goalsub_abbrev_tac`toSortedAList t`
  \\ DEP_REWRITE_TAC[Q.ISPEC`w2n`FOLDR_UPDATE_lookup]
  \\ simp[ALL_DISTINCT_MAP_FST_toSortedAList, ALOOKUP_toSortedAList]
  \\ simp[Abbr`t`, lookup_build_spt, domain_lookup, FUN_EQ_THM]
  \\ rw[]
  \\ qspec_then`k`mp_tac w2n_lt
  \\ gs[]
QED

val () = cv_auto_trans empty_account_state_def;

val cv_empty_account_state_thm = theorem "cv_empty_account_state_thm";

Definition lookup_account_def:
  lookup_account (accounts: evm_accounts) address = accounts address
End

Definition cv_lookup_account_def:
  cv_lookup_account (a:cv) (k:cv) =
  let v = cv_lookup k a in
    cv_if (cv_ispair v) (cv_snd v) (cv_empty_account_state (Num 0))
End

Theorem lookup_account_cv_rep[cv_rep]:
  ^from_account_state (lookup_account a k) =
  cv_lookup_account (from_evm_accounts a) (from_word k)
Proof
  gs[lookup_account_def, cv_lookup_account_def, GSYM cv_lookup_thm,
     from_word_def, from_evm_accounts_def, lookup_build_spt]
  \\ qspec_then`k`strip_assume_tac w2n_lt
  \\ simp[]
  \\ Cases_on`a k = empty_account_state`
  \\ gs[from_option_def, cv_empty_account_state_thm]
QED

Definition update_account_def:
  update_account (accounts: evm_accounts) address new_account =
    (address =+ new_account) accounts
End

Definition cv_update_account_def:
  cv_update_account (a:cv) (k:cv) (v:cv) =
  cv_if (cv_eq v (cv_empty_account_state (Num 0)))
    (cv_delete k a)
    (cv_insert k v a)
End

Theorem update_account_cv_rep[cv_rep]:
  from_evm_accounts (update_account a k v) =
  cv_update_account (from_evm_accounts a) (from_word k) (^from_account_state v)
Proof
  gs[from_evm_accounts_def, cv_update_account_def,
     update_account_def, from_word_def, cv_eq_def]
  \\ qmatch_goalsub_abbrev_tac`Num (COND ve _ _)`
  \\ `ve ⇔ v = empty_account_state`
  by metis_tac[cv_empty_account_state_thm,
               from_to_account_state,
               from_to_def]
  \\ simp[Abbr`ve`]
  \\ gs[GSYM cv_insert_thm, GSYM cv_delete_thm]
  \\ IF_CASES_TAC
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_delete, wf_insert, lookup_delete, lookup_insert,
          lookup_build_spt, APPLY_UPDATE_THM]
  \\ rw[] \\ gvs[]
  \\ TRY (qspec_then`k`strip_assume_tac w2n_lt \\ gs[] \\ NO_TAC)
  \\ qpat_x_assum`_ = empty_account_state`mp_tac \\ rw[] \\ gs[]
QED

Definition from_word_fset_def:
  from_word_fset (fs: 'a word fset) = from_num_fset (fIMAGE w2n fs)
End

Definition to_word_fset_def:
  to_word_fset cv = fIMAGE n2w $ to_num_fset cv
End

Theorem from_to_word_fset[cv_from_to]:
  from_to from_word_fset to_word_fset
Proof
  mp_tac from_to_num_fset
  \\ rw[from_to_def, from_word_fset_def, to_word_fset_def]
  \\ gs[GSYM fIMAGE_COMPOSE, o_DEF]
QED

Definition from_storage_key_def:
  from_storage_key (s: storage_key) =
  Num (w2n (case s of SK x y => word_join y x))
End

Definition to_storage_key_def:
  to_storage_key cv =
  let w: (256 + 160) word = to_word cv in
    SK ((160 >< 0) w) ((256 + 160 >< 160) w)
End

Theorem from_to_storage_key[cv_from_to]:
  from_to from_storage_key to_storage_key
Proof
  rw[from_to_def, from_storage_key_def, to_storage_key_def, to_word_def]
  \\ CASE_TAC \\ BBLAST_TAC
QED

Definition from_storage_key_fset_def:
  from_storage_key_fset (fs: storage_key fset) =
    from_num_fset (fIMAGE (λk. case k of SK a b => w2n (word_join b a)) fs)
End

Definition to_storage_key_fset_def:
  to_storage_key_fset cv =
  fIMAGE (λn.
    let w : (256 + 160) word = n2w n in
      SK ((160 >< 0) w) ((256 + 160 >< 160) w)
  ) $ to_num_fset cv
End

Theorem from_to_storage_key_fset[cv_from_to]:
  from_to from_storage_key_fset to_storage_key_fset
Proof
  mp_tac from_to_num_fset
  \\ rw[from_to_def, from_storage_key_fset_def, to_storage_key_fset_def]
  \\ gs[GSYM fIMAGE_COMPOSE, o_DEF]
  \\ qmatch_goalsub_abbrev_tac`fIMAGE f`
  \\ `f = I` suffices_by rw[]
  \\ simp[Abbr`f`, FUN_EQ_THM]
  \\ Cases \\ simp[]
  \\ BBLAST_TAC
QED

Theorem fINSERT_word_cv_rep[cv_rep]:
  from_word_fset (fINSERT e s) =
  cv_insert (from_word e) (from_unit ()) (from_word_fset s)
Proof
  rw[from_word_fset_def, fINSERT_num_cv_rep, from_word_def]
QED

Theorem fIN_word_cv_rep[cv_rep]:
  b2c (fIN e s) =
  cv_ispair (cv_lookup (from_word e) (from_word_fset s))
Proof
  rw[from_word_fset_def, GSYM fIN_num_cv_rep, from_word_def]
QED

Theorem fINSERT_storage_key_cv_rep[cv_rep]:
  from_storage_key_fset (fINSERT e s) =
  cv_insert (from_storage_key e) (from_unit ()) (from_storage_key_fset s)
Proof
  rw[from_storage_key_fset_def, GSYM fINSERT_num_cv_rep,
     from_storage_key_def] \\ CASE_TAC \\ rw[]
QED

Theorem fIN_storage_key_cv_rep[cv_rep]:
  b2c (fIN e s) =
  cv_ispair (cv_lookup (from_storage_key e) (from_storage_key_fset s))
Proof
  rw[from_storage_key_fset_def, GSYM fIN_num_cv_rep,
     from_storage_key_def]
  \\ AP_TERM_TAC
  \\ CASE_TAC \\ rw[]
  \\ rw[EQ_IMP_THM] >- (
       goal_assum(first_assum o mp_then Any mp_tac)
       \\ rw[] )
  \\ pop_assum mp_tac \\ CASE_TAC
  \\ qmatch_asmsub_rename_tac`fIN (SK e1 e2)`
  \\ qmatch_goalsub_rename_tac`fIN (SK d1 d2)`
  \\ strip_tac
  \\ `(d1, d2) = (e1, e2)` suffices_by rw[]
  \\ pop_assum mp_tac
  \\ simp[]
  \\ BBLAST_TAC
QED

val from_to_transaction_state = from_to_thm_for “:transaction_state”;

val () = “consume_gas n s” |>
  SIMP_CONV std_ss [consume_gas_def, bind_def, ignore_bind_def, LET_RATOR] |>
  cv_auto_trans;

val () = “refund_gas n s” |>
  SIMP_CONV std_ss [refund_gas_def, bind_def, ignore_bind_def, LET_RATOR] |>
  cv_auto_trans;

val () = “push_context c s” |>
  SIMP_CONV std_ss [
    push_context_def, bind_def, ignore_bind_def,
    LET_RATOR, COND_RATOR] |>
  cv_auto_trans;

val () = code_for_transfer_def |>
  ONCE_REWRITE_RULE[GSYM lookup_account_def] |>
  cv_auto_trans;

Theorem context_for_transfer_unfolded:
  context_for_transfer ctxt callerAddress incCaller code =
  ctxt with callParams :=
    ctxt.callParams with <|
      accounts := update_account
        ctxt.callParams.accounts callerAddress incCaller;
      code := code
    |>
Proof
  rw[context_for_transfer_def,
     context_component_equality,
     call_parameters_component_equality,
     update_account_def]
QED

val () = cv_auto_trans context_for_transfer_unfolded;

Triviality incCaller_unfolded:
  (caller: account_state) with nonce updated_by SUC =
  caller with nonce := SUC caller.nonce
Proof
  rw[account_state_component_equality]
QED

Triviality update_accounts:
  update_accounts ((a =+ b) o (c =+ d)) s =
  return () (s with accounts :=
    update_account (update_account s.accounts c d) a b)
Proof
  rw[update_accounts_def, return_def, update_account_def,
     transaction_state_component_equality]
QED

val () = “start_context x y c s” |>
  SIMP_CONV std_ss [
    start_context_def, bind_def, ignore_bind_def,
    COND_RATOR, LET_RATOR, C_DEF,
    incCaller_unfolded, update_accounts ] |>
  ONCE_REWRITE_RULE[GSYM lookup_account_def] |>
  cv_auto_trans;

val () = cv_auto_trans get_current_accesses_def;

val () = cv_auto_trans access_address_def;

val () = cv_auto_trans access_slot_def;

val () = “finish_current r s” |>
  SIMP_CONV std_ss [
    finish_current_def, bind_def, LET_RATOR
  ]
  |> cv_auto_trans;

val from_to_access_list_entry = from_to_thm_for “:access_list_entry”;

val from_to_transaction = from_to_thm_for “:transaction”;

val step_call_pre_def = “step_call t s” |>
  SIMP_CONV std_ss [
    step_call_def, bind_def, ignore_bind_def, LET_RATOR
  ]
  |> ONCE_REWRITE_RULE[GSYM lookup_account_def]
  |> cv_auto_trans_pre;

Theorem step_call_pre[cv_pre]:
  ∀t s. step_call_pre t s
Proof
  rw[step_call_pre_def, assert_def]
  \\ strip_tac \\ gvs[]
QED

(*
val step_create_pre_def = “step_create t s” |>
  SIMP_CONV std_ss [
    step_create_def, bind_def, ignore_bind_def, LET_RATOR
  ]
  |> ONCE_REWRITE_RULE[GSYM lookup_account_def]
  |> cv_auto_trans_pre;

val () = cv_auto_trans step_def;
*)

val _ = export_theory();
