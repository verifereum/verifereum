open HolKernel boolLib bossLib Parse dep_rewrite
     wordsTheory sptreeTheory alistTheory pairTheory
     combinTheory arithmeticTheory
     cv_transLib cv_typeLib cvTheory cv_typeTheory cv_stdTheory
     vfmTypesTheory;

val _ = new_theory "vfmState";

Type storage = “:bytes32 -> bytes32”;

Definition lookup_storage_def:
  lookup_storage k (s: storage) = s k
End

Definition update_storage_def:
  update_storage k v (s: storage) = (k =+ v) s
End

Definition empty_storage_def:
  empty_storage: bytes32 -> bytes32 = K 0w
End

Definition storage_empty_def:
  storage_empty (s: storage) = (s = empty_storage)
End

(* cv compute translation for storage *)

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

Theorem build_spt_empty_iff:
  ∀n. build_spt z n s = LN ⇔ (∀m. m < n ==> s (n2w m) = z)
Proof
  Induct \\ gvs[build_spt_def]
  \\ rw[EQ_IMP_THM]
  \\ Cases_on`m = n` \\ gvs[]
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

Definition cv_lookup_storage_def:
  cv_lookup_storage (k:cv) (s:cv) =
  let v = cv_lookup k s in
    cv_if (cv_ispair v) (cv_snd v) (Num 0)
End

Theorem lookup_storage_cv_rep[cv_rep]:
  from_word (lookup_storage k s) =
  cv_lookup_storage (from_word k) (from_storage s)
Proof
  gs[lookup_storage_def, cv_lookup_storage_def, GSYM cv_lookup_thm,
     from_word_def, from_storage_def, lookup_build_spt]
  \\ qspec_then`k`mp_tac w2n_lt
  \\ simp[]
  \\ Cases_on`s k = 0w`
  \\ gs[from_option_def, from_word_def]
QED

Definition cv_update_storage_def:
  cv_update_storage (k:cv) (v:cv) (s:cv) =
  cv_if (cv_eq v (Num 0))
    (cv_delete k s)
    (cv_insert k v s)
End

Theorem update_storage_cv_rep[cv_rep]:
  from_storage (update_storage k v s) =
  cv_update_storage (from_word k) (from_word v) (from_storage s)
Proof
  gs[from_storage_def, cv_update_storage_def,
     update_storage_def, from_word_def, cv_eq_def]
  \\ `Num (w2n v) = from_word v` by simp[from_word_def]
  \\ pop_assum SUBST1_TAC
  \\ gs[GSYM cv_insert_thm, GSYM cv_delete_thm]
  \\ IF_CASES_TAC
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_delete, wf_insert, lookup_delete, lookup_insert,
          lookup_build_spt, APPLY_UPDATE_THM]
  \\ rw[] \\ gvs[]
  \\ TRY (qspec_then`k`strip_assume_tac w2n_lt \\ gs[] \\ NO_TAC)
  \\ qpat_x_assum`_ = 0w`mp_tac \\ rw[] \\ gs[]
QED

Theorem from_sptree_eq_Num_iff:
  from_sptree_sptree_spt f m = Num n <=> (m = LN ∧ n = 0)
Proof
  Cases_on`m` \\ rw[from_sptree_sptree_spt_def]
QED

Theorem storage_empty_cv_rep[cv_rep]:
  b2c (storage_empty s) =
    cv_eq (from_storage s) (Num 0)
Proof
  Cases_on`storage_empty s`
  \\ gs[from_storage_def, cv_eq_def,
        storage_empty_def, from_sptree_sptree_spt_def]
  \\ rw[from_sptree_eq_Num_iff, build_spt_empty_iff]
  \\ gs[empty_storage_def, FUN_EQ_THM]
  \\ Cases_on`x` \\ gs[]
QED

(* -- *)

Datatype:
  account_state =
  <| nonce   : num
   ; balance : num
   ; storage : storage
   ; code    : byte list
   |>
End

Definition empty_account_state_def:
  empty_account_state =
    <| nonce := 0
     ; balance := 0
     ; storage := empty_storage
     ; code := []
     |>
End

Type evm_accounts = “:address -> account_state”

Definition lookup_account_def:
  lookup_account address (accounts: evm_accounts) = accounts address
End

Definition update_account_def:
  update_account address new_account (accounts: evm_accounts) =
    (address =+ new_account) accounts
End

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

Definition cv_lookup_account_def:
  cv_lookup_account (k:cv) (a:cv) =
  let v = cv_lookup k a in
    cv_if (cv_ispair v) (cv_snd v) (cv_empty_account_state (Num 0))
End

Theorem lookup_account_cv_rep[cv_rep]:
  ^from_account_state (lookup_account k a) =
  cv_lookup_account (from_word k) (from_evm_accounts a)
Proof
  gs[lookup_account_def, cv_lookup_account_def, GSYM cv_lookup_thm,
     from_word_def, from_evm_accounts_def, lookup_build_spt]
  \\ qspec_then`k`strip_assume_tac w2n_lt
  \\ simp[]
  \\ Cases_on`a k = empty_account_state`
  \\ gs[from_option_def, cv_empty_account_state_thm]
QED

Definition cv_update_account_def:
  cv_update_account (k:cv) (v:cv) (a:cv) =
  cv_if (cv_eq v (cv_empty_account_state (Num 0)))
    (cv_delete k a)
    (cv_insert k v a)
End

Theorem update_account_cv_rep[cv_rep]:
  from_evm_accounts (update_account k v a) =
  cv_update_account (from_word k) (^from_account_state v) (from_evm_accounts a)
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

Definition empty_accounts_def:
  empty_accounts (a: address) = empty_account_state
End

Theorem build_spt_empty_accounts[simp]:
  ∀n. build_spt empty_account_state n empty_accounts = LN
Proof
  Induct \\ rw[build_spt_def]
  \\ gs[empty_accounts_def]
QED

Theorem empty_accounts_cv_rep[cv_rep]:
  from_evm_accounts empty_accounts = Num 0
Proof
  rw[from_evm_accounts_def, from_sptree_sptree_spt_def]
QED

val _ = export_theory();
