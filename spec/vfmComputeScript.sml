open HolKernel boolLib bossLib Parse dep_rewrite blastLib cv_typeTheory
cv_transLib cv_typeLib cvTheory cv_stdTheory pairTheory combinTheory
optionTheory sumTheory listTheory byteTheory wordsTheory alistTheory
arithmeticTheory finite_setTheory sptreeTheory whileTheory
recursiveLengthPrefixTheory merklePatriciaTrieTheory vfmRootTheory
vfmContextTheory vfmStateTheory vfmTransactionTheory vfmExecutionTheory
vfmTypesTheory;

val _ = new_theory "vfmCompute";

(* TODO: move *)

Theorem word_lsl_modexp:
  word_lsl (w:'a word) n =
  if n < dimindex(:'a) then
    n2w (modexp 2 n (dimword(:'a)) (w2n w))
  else 0w
Proof
  Cases_on`w`
  \\ simp[word_lsl_n2w]
  \\ DEP_REWRITE_TAC[modexp_exp]
  \\ rw[]
  \\ fs[dimword_def]
  \\ gvs[]
QED

Theorem size_list_to_num_set:
  size (list_to_num_set ls) = LENGTH (nub ls)
Proof
  Induct_on`ls`
  \\ gs[list_to_num_set_def, nub_def, size_insert, domain_list_to_num_set]
  \\ rw[]
QED

Theorem toSet_fEMPTY[simp]:
  toSet fEMPTY = {}
Proof
  rw[toSet_def]
QED

Theorem toSet_fINSERT:
  toSet (fINSERT x s) = x INSERT (toSet s)
Proof
  rw[toSet_def, pred_setTheory.EXTENSION]
QED

Theorem CARD_toSet:
  CARD (toSet s) = fCARD s
Proof
  Induct_on`s` \\ gs[toSet_fINSERT, fIN_IN]
QED

Theorem toSet_fIMAGE:
  toSet (fIMAGE f s) = IMAGE f (toSet s)
Proof
  rw[toSet_def, pred_setTheory.EXTENSION, EQ_IMP_THM]
  \\ metis_tac[]
QED

Theorem fCARD_num_cv_rep[cv_rep]:
  Num (fCARD (s: num fset)) =
  cv_size' (from_num_fset s)
Proof
  rw[from_num_fset_def, GSYM cv_size'_thm, size_list_to_num_set]
  \\ irule EQ_SYM
  \\ irule(SIMP_RULE std_ss [quotientTheory.FUN_REL] fCARD_relates)
  \\ simp[FSET_def]
QED

(* -- *)

Definition to_transient_storage_def:
  to_transient_storage cv : transient_storage =
  let t = to_sptree_spt to_storage cv in
    FOLDR (λ(k,v) f. (n2w k =+ v) f) (λk. empty_storage) (toSortedAList t)
End

Definition from_transient_storage_def:
  from_transient_storage (t: transient_storage) =
  from_sptree_sptree_spt from_storage
    (build_spt empty_storage (dimword (:160)) t)
End

val from_to_transient_storage_spt = from_to_thm_for “:storage num_map”;

Theorem from_to_transient_storage[cv_from_to]:
  from_to from_transient_storage to_transient_storage
Proof
  rw[from_to_def, from_transient_storage_def, to_transient_storage_def]
  \\ rw[from_to_transient_storage_spt |> REWRITE_RULE[from_to_def]]
  \\ qmatch_goalsub_abbrev_tac`toSortedAList t`
  \\ DEP_REWRITE_TAC[Q.ISPEC`w2n`FOLDR_UPDATE_lookup]
  \\ simp[ALL_DISTINCT_MAP_FST_toSortedAList, ALOOKUP_toSortedAList]
  \\ simp[Abbr`t`, lookup_build_spt, domain_lookup, FUN_EQ_THM]
  \\ rw[]
  \\ qspec_then`k`mp_tac w2n_lt
  \\ gs[]
QED

Theorem build_spt_empty_transient_storage[simp]:
  ∀n. build_spt empty_storage n empty_transient_storage = LN
Proof
  Induct \\ rw[build_spt_def]
  \\ gs[empty_transient_storage_def]
QED

Theorem empty_transient_storage_cv_rep[cv_rep]:
  from_transient_storage empty_transient_storage = Num 0
Proof
  rw[from_transient_storage_def, from_sptree_sptree_spt_def]
QED

Definition cv_lookup_transient_storage_def:
  cv_lookup_transient_storage (a:cv) (t:cv) =
  let v = cv_lookup a t in
    cv_if (cv_ispair v) (cv_snd v) (Num 0)
End

Theorem lookup_transient_storage_cv_rep[cv_rep]:
  from_storage (lookup_transient_storage k t) =
  cv_lookup_transient_storage (from_word k) (from_transient_storage t)
Proof
  gs[lookup_transient_storage_def, cv_lookup_transient_storage_def,
     from_transient_storage_def,
     GSYM cv_lookup_thm, from_word_def, from_storage_def, lookup_build_spt]
  \\ qspec_then`k`strip_assume_tac w2n_lt
  \\ gs[]
  \\ Cases_on`t k = empty_storage`
  \\ gs[from_option_def, from_storage_def, from_sptree_eq_Num_iff]
QED

Definition cv_update_transient_storage_def:
  cv_update_transient_storage (k:cv) (v:cv) (a:cv) =
  cv_if (cv_eq v (Num 0))
    (cv_delete k a)
    (cv_insert k v a)
End

Theorem update_transient_storage_cv_rep[cv_rep]:
  from_transient_storage (update_transient_storage k v a) =
  cv_update_transient_storage (from_word k) (from_storage v)
    (from_transient_storage a)
Proof
  gs[from_transient_storage_def, cv_update_transient_storage_def,
     update_transient_storage_def, from_word_def, cv_eq_def]
  \\ qmatch_goalsub_abbrev_tac`Num (COND ve _ _)`
  \\ `ve ⇔ v = empty_storage` by (
    simp[from_storage_def, Abbr`ve`, from_sptree_eq_Num_iff,
         build_spt_empty_iff, FUN_EQ_THM, empty_storage_def]
    \\ simp[EQ_IMP_THM] \\ strip_tac
    \\ Cases \\ gs[] )
  \\ simp[Abbr`ve`]
  \\ gs[GSYM cv_insert_thm, GSYM cv_delete_thm]
  \\ IF_CASES_TAC
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_delete, wf_insert, lookup_delete, lookup_insert,
          lookup_build_spt, APPLY_UPDATE_THM]
  \\ rw[] \\ gvs[]
  \\ TRY (qspec_then`k`strip_assume_tac w2n_lt \\ gs[] \\ NO_TAC)
  \\ qpat_x_assum`_ = empty_storage`mp_tac \\ rw[] \\ gs[]
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

Theorem from_list_from_word_MAP_w2n:
  from_list from_word l =
  from_list Num (MAP w2n l)
Proof
  Induct_on`l`
  \\ rw[cv_typeTheory.from_list_def, cv_typeTheory.from_word_def]
QED

Theorem fset_ABS_word_cv_rep[cv_rep]:
  from_word_fset (fset_ABS l) =
  cv_list_to_num_set (from_list from_word l)
Proof
  rw[from_word_fset_def, from_num_fset_def,
     from_list_from_word_MAP_w2n,
     GSYM cv_list_to_num_set_thm]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_list_to_num_set, lookup_list_to_num_set, MEM_fset_REP]
  \\ simp[GSYM fromSet_set, IN_fromSet, MEM_MAP]
  \\ metis_tac[]
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

Theorem SK_cv_rep[cv_rep]:
  from_storage_key (SK x y) =
  cv_add (cv_mul (from_word y) (cv_exp (Num 2) (Num 160))) (from_word x)
Proof
  rw[from_storage_key_def]
  \\ `160 = dimindex (:160)` by rw[]
  \\ pop_assum SUBST1_TAC
  \\ rw[GSYM cv_primTheory.cv_word_join_thm, from_word_def]
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

Theorem from_list_from_storage_key_MAP_w2n:
  from_list from_storage_key l =
  from_list Num (MAP (λs. w2n (case s of SK x y => word_join y x)) l)
Proof
  Induct_on`l`
  \\ rw[cv_typeTheory.from_list_def, from_storage_key_def]
QED

Theorem fset_ABS_storage_key_cv_rep[cv_rep]:
  from_storage_key_fset (fset_ABS l) =
  cv_list_to_num_set (from_list from_storage_key l)
Proof
  rw[from_storage_key_fset_def, from_num_fset_def,
     from_list_from_storage_key_MAP_w2n,
     GSYM cv_list_to_num_set_thm]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_list_to_num_set, lookup_list_to_num_set, MEM_fset_REP]
  \\ simp[GSYM fromSet_set, IN_fromSet, MEM_MAP, CaseEq"storage_key"]
  \\ rw[PULL_EXISTS] \\ gs[]
  \\ Cases_on`s` \\ gs[]
QED

Theorem fINSERT_word_cv_rep[cv_rep]:
  from_word_fset (fINSERT e s) =
  cv_insert (from_word e) (Num 0) (from_word_fset s)
Proof
  rw[from_word_fset_def, fINSERT_num_cv_rep, from_word_def]
QED

Theorem fIN_word_cv_rep[cv_rep]:
  b2c (fIN e s) =
  cv_ispair (cv_lookup (from_word e) (from_word_fset s))
Proof
  rw[from_word_fset_def, GSYM fIN_num_cv_rep, from_word_def]
QED

Theorem fUNION_word_cv_rep[cv_rep]:
  from_word_fset (fUNION s1 s2) =
  cv_union (from_word_fset s1) (from_word_fset s2)
Proof
  rw[from_word_fset_def, fIMAGE_fUNION, fUNION_num_cv_rep]
QED

Theorem fEMPTY_word_cv_rep[cv_rep]:
  from_word_fset fEMPTY = Num 0
Proof
  rw[from_word_fset_def, fEMPTY_num_cv_rep]
QED

Theorem fINSERT_storage_key_cv_rep[cv_rep]:
  from_storage_key_fset (fINSERT e s) =
  cv_insert (from_storage_key e) (Num 0) (from_storage_key_fset s)
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

Theorem fUNION_storage_key_cv_rep[cv_rep]:
  from_storage_key_fset (fUNION s1 s2) =
  cv_union (from_storage_key_fset s1) (from_storage_key_fset s2)
Proof
  rw[from_storage_key_fset_def, fIMAGE_fUNION, fUNION_num_cv_rep]
QED

Theorem fEMPTY_storage_key_cv_rep[cv_rep]:
  from_storage_key_fset fEMPTY = Num 0
Proof
  rw[from_storage_key_fset_def, fEMPTY_num_cv_rep]
QED

Theorem fCARD_word_cv_rep[cv_rep]:
  Num (fCARD s) = cv_size' (from_word_fset s)
Proof
  rw[from_word_fset_def, GSYM fCARD_num_cv_rep, GSYM CARD_toSet, toSet_fIMAGE]
  \\ irule EQ_SYM
  \\ irule pred_setTheory.CARD_INJ_IMAGE
  \\ simp[]
QED

Theorem fCARD_storage_key_cv_rep[cv_rep]:
  Num (fCARD s) = cv_size' (from_storage_key_fset s)
Proof
  rw[from_storage_key_fset_def, GSYM fCARD_num_cv_rep,
     GSYM CARD_toSet, toSet_fIMAGE]
  \\ irule EQ_SYM
  \\ irule pred_setTheory.CARD_INJ_IMAGE
  \\ simp[]
  \\ Cases \\ Cases
  \\ simp[EQ_IMP_THM]
  \\ blastLib.BBLAST_TAC
QED

(* TODO: does this already exist? *)
Definition domain_list_def:
  domain_list LN = [] ∧
  domain_list (LS _) = [0n] ∧
  domain_list (BN t1 t2) =
     MAP (λn. 2 * n + 2) (domain_list t1) ++
     MAP (λn. 2 * n + 1) (domain_list t2) ∧
  domain_list (BS t1 v t2) =
     0::
     MAP (λn. 2 * n + 2) (domain_list t1) ++
     MAP (λn. 2 * n + 1) (domain_list t2)
End

val () = cv_auto_trans domain_list_def;

val cv_domain_list_thm = theorem"cv_domain_list_thm";

Theorem set_domain_list:
  set (domain_list t) = domain t
Proof
  Induct_on`t` \\ rw[domain_list_def, LIST_TO_SET_MAP]
  \\ rw[pred_setTheory.EXTENSION] \\ metis_tac[]
QED

Definition MAP_word_join_num_def:
  MAP_word_join_num x ls =
  MAP (w2n : (256 + 160) word -> num o flip word_join x o n2w) ls
End

val () = MAP_word_join_num_def |> SIMP_RULE std_ss [combinTheory.C_DEF] |> cv_auto_trans;
val cv_MAP_word_join_num_thm = theorem "cv_MAP_word_join_num_thm";

Theorem from_storage_key_fset_fIMAGE_SK_cv_rep[cv_rep]:
  from_storage_key_fset (fIMAGE (SK x) s) =
  cv_list_to_num_set $
    cv_MAP_word_join_num (from_word x) (cv_domain_list (from_word_fset s))
Proof
  rw[from_storage_key_fset_def, from_num_fset_def,
     from_word_fset_def, GSYM cv_domain_list_thm,
     GSYM cv_MAP_word_join_num_thm,
     GSYM cv_list_to_num_set_thm]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_list_to_num_set, lookup_list_to_num_set,
          MEM_fset_REP, MAP_word_join_num_def, MEM_MAP,
          set_domain_list, domain_list_to_num_set, PULL_EXISTS]
  \\ metis_tac[]
QED

val from_to_execution_state = from_to_thm_for “:execution_state”;

val sign_extend_pre_def = cv_auto_trans_pre sign_extend_def;

Theorem sign_extend_pre[cv_pre]:
  sign_extend_pre n w
Proof
  rw[sign_extend_pre_def, NULL_EQ]
QED

val () = cv_auto_trans modexp_def;

val () = cv_auto_trans address_for_create_def;

val () = cv_auto_trans address_for_create2_def;

val () = “get_gas_left s” |>
  SIMP_CONV std_ss [get_gas_left_def, bind_def]
  |> cv_auto_trans;

val () = “get_callee s” |>
  SIMP_CONV std_ss [get_callee_def, bind_def]
  |> cv_auto_trans;

val () = “get_caller s” |>
  SIMP_CONV std_ss [get_caller_def, bind_def]
  |> cv_auto_trans;

val () = “get_value s” |>
  SIMP_CONV std_ss [get_value_def, bind_def]
  |> cv_auto_trans;

val () = “get_output_to s” |>
  SIMP_CONV std_ss [get_output_to_def, bind_def]
  |> cv_auto_trans;

val () = “get_return_data s” |>
  SIMP_CONV std_ss [get_return_data_def, bind_def]
  |> cv_auto_trans;

val () = “get_return_data_check x y s” |>
  SIMP_CONV std_ss [get_return_data_check_def, bind_def, ignore_bind_def]
  |> cv_auto_trans;

val () = “set_return_data r s” |>
  SIMP_CONV std_ss [set_return_data_def, bind_def, LET_RATOR]
  |> cv_auto_trans;

val () = “get_static s” |>
  SIMP_CONV std_ss [get_static_def, bind_def]
  |> cv_auto_trans;

val () = “get_code s” |>
  SIMP_CONV std_ss [get_code_def, bind_def]
  |> cv_auto_trans;

val () = “get_current_code s” |>
  SIMP_CONV std_ss [get_current_code_def, bind_def]
  |> cv_auto_trans;

val () = “get_call_data s” |>
  SIMP_CONV std_ss [get_call_data_def, bind_def]
  |> cv_auto_trans;

val () = “set_jump_dest j s” |>
  SIMP_CONV std_ss [set_jump_dest_def, bind_def]
  |> cv_auto_trans;

val () = “push_logs ls s” |>
  SIMP_CONV std_ss [push_logs_def, bind_def, C_DEF]
  |> cv_auto_trans;

val () = “update_gas_refund (a, b) s” |>
  SIMP_CONV std_ss [update_gas_refund_def, bind_def]
  |> cv_auto_trans;

val () = “consume_gas n s” |>
  SIMP_CONV std_ss [consume_gas_def, bind_def, ignore_bind_def, LET_RATOR] |>
  cv_auto_trans;

val () = “unuse_gas n s” |>
  SIMP_CONV std_ss [unuse_gas_def, bind_def, ignore_bind_def, LET_RATOR] |>
  cv_auto_trans;

val () = “pop_stack n s” |>
  SIMP_CONV std_ss [pop_stack_def, bind_def, ignore_bind_def, LET_RATOR] |>
  cv_auto_trans;

val () = “push_stack v s” |>
  SIMP_CONV std_ss [
    push_stack_def, bind_def, ignore_bind_def, LET_RATOR
  ] |> cv_auto_trans;

val () = “precompile_identity s” |>
   SIMP_CONV std_ss [
       precompile_identity_def, bind_def, ignore_bind_def, LET_RATOR
     ] |> cv_auto_trans;

val () = “precompile_modexp s” |>
   SIMP_CONV std_ss [
       precompile_modexp_def, bind_def, ignore_bind_def, LET_RATOR
     ] |> cv_auto_trans;

Theorem pop_stack_INL_LENGTH:
  pop_stack n s = (INL x, y) ⇒
  LENGTH x = n ∧
  s.contexts ≠ [] ∧
  n ≤ LENGTH (HD s.contexts).stack
Proof
  rw[pop_stack_def, bind_def, ignore_bind_def, get_current_context_def,
     fail_def, return_def, assert_def, CaseEq"sum", CaseEq"prod"]
  \\ rw[LENGTH_TAKE_EQ]
QED

val from_to_access_list_entry = from_to_thm_for “:access_list_entry”;

val from_to_transaction = from_to_thm_for “:transaction”;

val () = cv_auto_trans effective_gas_price_def;

val from_to_memory_expansion_info = from_to_thm_for “:memory_expansion_info”;

val () = “memory_expansion_info x y s” |>
  SIMP_CONV std_ss [
    memory_expansion_info_def, bind_def, ignore_bind_def, LET_RATOR
  ] |> cv_auto_trans;

val () = “expand_memory x s” |>
  SIMP_CONV std_ss [
    expand_memory_def, bind_def, ignore_bind_def
  ] |> cv_auto_trans;

val () = “read_memory x y s” |>
  SIMP_CONV std_ss [
    read_memory_def, bind_def
  ] |> cv_auto_trans;

val () = “write_memory x y s” |>
  SIMP_CONV std_ss [
    write_memory_def, bind_def, LET_RATOR
  ] |> cv_auto_trans;

val () = “write_storage x y z s” |>
  SIMP_CONV std_ss [ write_storage_def, update_accounts_def ]
  |> cv_auto_trans;

val () = “write_transient_storage x y z s” |>
  SIMP_CONV std_ss [ write_transient_storage_def, bind_def, LET_RATOR ]
  |> cv_auto_trans;

val () = “assert_not_static s” |>
  SIMP_CONV std_ss [
    assert_not_static_def, bind_def, ignore_bind_def
  ] |> cv_auto_trans;

val () = transfer_value_def |>
  SIMP_RULE std_ss [combinTheory.C_DEF] |>
  cv_auto_trans;

val () = “step_stop s” |>
  SIMP_CONV std_ss [
    step_stop_def, bind_def, ignore_bind_def
  ] |> cv_auto_trans;

(*
  set_goal([], pre_a)
*)
fun step_x_pre_tac pre_def =
  rw[pre_def, assert_def, LENGTH_TL]
  \\ TRY strip_tac \\ gvs[]
  \\ drule pop_stack_INL_LENGTH
  \\ rw[] \\ strip_tac \\ gvs[]

Triviality LET_PROD_RATOR:
  (let (x,y) = M in N x y) b = let (x,y) = M in N x y b
Proof
  rw[LET_THM, UNCURRY]
QED

Triviality LET_UNCURRY:
  (let (x,y) = M in N x y) = let p = M; x = FST p; y = SND p in N x y
Proof
  rw[UNCURRY]
QED

val option_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="option",Tyop="option"}));

val prod_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="pair",Tyop="prod"}));

val return_destination_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vfmContext",Tyop="return_destination"}));

fun mconv def =
  SIMP_CONV std_ss [
    def, copy_to_memory_def,
    bind_def,
    ignore_bind_def,
    COND_RATOR,
    LET_RATOR,
    LET_PROD_RATOR,
    option_CASE_rator,
    LET_UNCURRY
];

fun trans_step_x need_pre def = let
  val const = def |> SPEC_ALL |> concl |> lhs
  val stype = #1 $ dom_rng $ type_of const
  val s = mk_var("s", stype)
  val tm = mk_comb(const, s)
  val xdef = mconv def tm
in
  if need_pre then let
    val pre_def = cv_auto_trans_pre xdef
    val pre_a = pre_def |> SPEC_ALL |> concl |> lhs
    val pre_name = pre_a |> strip_comb |> #1 |> dest_const |> #1
  in
    store_thm(pre_name ^ "[cv_pre]", pre_a, step_x_pre_tac pre_def)
  end
  else
    (cv_auto_trans xdef; TRUTH)
end
val tf = trans_step_x false;
val tt = trans_step_x true;

val () = cv_auto_trans $ INST_TYPE[alpha |-> “:(256)”] word_exp_tailrec_def;

val () = cv_auto_trans $ INST_TYPE[alpha |-> “:(256)”] word_exp_tailrec;

val th = tt step_exp_def;
val th = tt step_keccak256_def;
val th = tt step_sload_def;
val th = tf step_sstore_gas_consumption_def;
val th = tt step_sstore_def;
val th = tt step_balance_def;
val th = tt step_call_data_load_def;
val th = tt step_return_data_copy_def;
val th = tt step_ext_code_size_def;
val th = tt step_ext_code_copy_def;
val th = tt step_ext_code_hash_def;
val th = tt step_block_hash_def;
val th = tf step_self_balance_def;
val th = tt step_mload_def;
val th = tt step_mstore_def;
val th = tt step_jump_def;
val th = tt step_jumpi_def;
val th = tf step_push_def;
val th = tf step_pop_def;
val th = tt step_dup_def;
val th = tt step_swap_def;
val th = tt step_log_def;
val th = tt step_return_def;
val th = tf step_invalid_def;
val th = tt step_self_destruct_def;

val () = “abort_unuse n s” |>
  SIMP_CONV std_ss [
    abort_unuse_def, bind_def, ignore_bind_def
  ] |> cv_auto_trans;

val () = “abort_create_exists x y s” |>
  SIMP_CONV std_ss [
    abort_create_exists_def, bind_def, ignore_bind_def
  ] |> cv_auto_trans;

val () = “proceed_create a b c d e f g s” |>
  SIMP_CONV std_ss [
    proceed_create_def, bind_def, ignore_bind_def, LET_RATOR, o_DEF
  ] |> cv_auto_trans;

val th = tt step_create_def;

val () = “abort_call_value x s” |>
  SIMP_CONV std_ss [
    abort_call_value_def, bind_def, ignore_bind_def
  ] |> cv_auto_trans;

val () = “dispatch_precompiles a s” |>
  SIMP_CONV std_ss [
    dispatch_precompiles_def, COND_RATOR
  ] |> cv_auto_trans;

val () = “proceed_call a b c d e f g h i s” |>
  SIMP_CONV std_ss [
    proceed_call_def, bind_def, ignore_bind_def, LET_RATOR, COND_RATOR
  ] |> cv_auto_trans;

val th = tt step_call_def;

val step_inst_pre_def = step_inst_def |>
  ONCE_REWRITE_RULE[FUN_EQ_THM] |>
  SIMP_RULE std_ss [
    step_monop_def,
    step_binop_def,
    step_modop_def,
    word_lsl_modexp,
    with_zero_def,
    step_context_def,
    step_msgParams_def,
    step_txParams_def,
    step_copy_to_memory_def,
    copy_to_memory_def,
    bind_def, ignore_bind_def, LET_RATOR,
    LET_PROD_RATOR, option_CASE_rator, LET_UNCURRY
  ] |> cv_auto_trans_pre;

Theorem step_inst_pre[cv_pre]:
  step_inst_pre i s
Proof
  simp[step_inst_pre_def]
  \\ rpt gen_tac
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ TRY(disch_then(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  \\ rpt strip_tac \\ gvs[]
  \\ drule pop_stack_INL_LENGTH \\ gvs[]
QED

val () = “inc_pc_or_jump n s” |>
  SIMP_CONV std_ss [
    inc_pc_or_jump_def, bind_def, ignore_bind_def,
    LET_RATOR, COND_RATOR, option_CASE_rator] |>
  cv_auto_trans;

val () = “pop_and_incorporate_context b s” |>
  SIMP_CONV std_ss [
    pop_and_incorporate_context_def,
    bind_def, ignore_bind_def, COND_RATOR
  ] |> cv_auto_trans;

val () = “handle_create e s” |>
  SIMP_CONV std_ss [
    handle_create_def,
    bind_def, ignore_bind_def, LET_RATOR,
    update_accounts_def, COND_RATOR, LET_PROD_RATOR,
    option_CASE_rator,
    prod_CASE_rator, return_destination_CASE_rator
  ] |> cv_auto_trans;

val () = “handle_exception e s” |>
  SIMP_CONV std_ss [
    handle_exception_def,
    bind_def, ignore_bind_def, LET_RATOR,
    update_accounts_def, COND_RATOR, LET_PROD_RATOR,
    prod_CASE_rator, return_destination_CASE_rator
  ] |> cv_auto_trans;

val () = “handle_step e s” |>
  SIMP_CONV std_ss [
    handle_step_def, bind_def, ignore_bind_def
  ] |> cv_auto_trans;

val () = “step s” |>
  SIMP_CONV std_ss [
    step_def, bind_def, ignore_bind_def, LET_RATOR,
    COND_RATOR, option_CASE_rator, handle_def
  ] |> cv_auto_trans;

val () = initial_access_sets_def
 |> SIMP_RULE std_ss [
      GSYM fset_ABS_MAP,
      fBIGUNION_fset_ABS_FOLDL
    ] |> cv_auto_trans;

val () = cv_auto_trans initial_tx_params_def;

val () = initial_state_def |>
  ONCE_REWRITE_RULE[GSYM lookup_account_def] |>
  ONCE_REWRITE_RULE[GSYM update_account_def] |>
  cv_auto_trans;

Definition run_with_fuel_def:
  run_with_fuel n (r, s) =
  if ISR r then SOME (OUTR r, s, n)
  else case n of
  | 0 => NONE
  | SUC m => run_with_fuel m (step s)
End

val run_with_fuel_pre_def = cv_auto_trans_pre run_with_fuel_def;

val run_with_fuel_ind = theorem"run_with_fuel_ind";

Theorem run_with_fuel_pre[cv_pre]:
  ∀n v. run_with_fuel_pre n v
Proof
  simp[pairTheory.FORALL_PROD]
  \\ ho_match_mp_tac run_with_fuel_ind
  \\ rpt strip_tac
  \\ rw[Once run_with_fuel_pre_def]
QED

Definition run_n_def:
  run_n n s = FUNPOW (step o SND) n (INL (), s)
End

val () = cv_auto_trans run_n_def;

Theorem run_SOME_run_n:
  run s = SOME p ⇔
  ISR (FST p) ∧
  ∃n. run_n n s = p ∧
      ∀m. m < n ⇒ ISL (FST (run_n m s))
Proof
  simp[run_def, run_n_def, EQ_IMP_THM]
  \\ conj_tac >- (
    strip_tac
    \\ imp_res_tac OWHILE_WHILE
    \\ imp_res_tac OWHILE_ENDCOND
    \\ Cases_on`p` \\ gs[]
    \\ qexists_tac`LEAST n. ~(ISL o FST) (FUNPOW (step o SND) n (INL (), s))`
    \\ DEP_REWRITE_TAC[GSYM WHILE_FUNPOW]
    \\ gs[combinTheory.o_DEF]
    \\ numLib.LEAST_ELIM_TAC \\ gs[]
    \\ conj_asm1_tac
    >- (
      spose_not_then strip_assume_tac
      \\ qmatch_assum_abbrev_tac `OWHILE G f z = _`
      \\ `∀n. G (FUNPOW f n z)` by  (
        rw[Abbr`G`] \\ gs[sumTheory.NOT_ISR_ISL] )
      \\ imp_res_tac OWHILE_EQ_NONE
      \\ gs[] )
    \\ rw[] )
  \\ simp[OWHILE_def]
  \\ strip_tac
  \\ conj_asm1_tac >- ( qexists_tac`n` \\ gs[] )
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- metis_tac[]
  \\ rw[]
  \\ qmatch_goalsub_rename_tac`FUNPOW _ m`
  \\ Cases_on`m < n` >- metis_tac[sumTheory.NOT_ISR_ISL]
  \\ Cases_on`n < m` >- metis_tac[sumTheory.NOT_ISL_ISR, pairTheory.FST]
  \\ `n = m` by gs[]
  \\ gs[]
QED

Theorem run_with_fuel_to_zero_aux[local]:
  ∀n x s z t m.
    run_with_fuel n (x, s) = SOME (z, t, m) ∧
    ISL (FST (x, s)) ∧ m = 0 ⇒
    run_n n (SND (x, s)) = (INR z, t) ∧
    (∀l. l < n ⇒ ISL (FST (run_n l (SND (x, s)))))
Proof
  ho_match_mp_tac run_with_fuel_ind
  \\ gs[]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ qhdtm_x_assum`run_with_fuel`mp_tac
  \\ simp[Once run_with_fuel_def]
  \\ Cases_on`r` \\ gs[]
  \\ gs[num_case_eq, run_n_def]
  \\ disch_then strip_assume_tac
  \\ gvs[]
  \\ simp[Once FUNPOW]
  \\ Cases_on`step s` \\ gs[]
  \\ qmatch_assum_rename_tac`step s = (x,y)`
  \\ Cases_on`x` \\ gs[]
  >- ( Cases \\ simp[Once FUNPOW] )
  \\ qhdtm_x_assum`run_with_fuel`mp_tac
  \\ rw[Once run_with_fuel_def]
QED

Theorem run_with_fuel_to_zero:
  run_with_fuel n (INL (), s) = SOME (z, t, 0) ⇒
  run_n n s = (INR z, t) ∧
  (∀m. m < n ⇒ ISL (FST (run_n m s)))
Proof
  strip_tac
  \\ drule run_with_fuel_to_zero_aux
  \\ gs[]
QED

Theorem run_with_fuel_add:
  ∀n q r a b c m.
  run_with_fuel n (q,r) = SOME (a,b,c) ⇒
  run_with_fuel (n + m) (q,r) = SOME (a,b,c + m)
Proof
  ho_match_mp_tac run_with_fuel_ind
  \\ rw[]
  \\ Cases_on`r` \\ gvs[run_with_fuel_def, num_case_eq]
  \\ first_x_assum(qspec_then`m`(goal_assum o C (mp_then Any mp_tac)))
  \\ simp[]
QED

Theorem run_with_fuel_sub:
  ∀n q r a b c.
  run_with_fuel n (q,r) = SOME (a,b,c) ⇒
  run_with_fuel (n - c) (q,r) = SOME (a,b,0)
Proof
  ho_match_mp_tac run_with_fuel_ind
  \\ rw[]
  \\ Cases_on`r` \\ gvs[run_with_fuel_def, num_case_eq]
  \\ Cases_on`m < c` \\ gs[] >- (
    `m - c = 0` by simp[]
    \\ Cases_on`step s`
    \\ gs[run_with_fuel_def] )
  \\ first_x_assum(goal_assum o C (mp_then Any mp_tac))
  \\ simp[]
QED

Theorem run_with_fuel_equal:
  ∀n q r a b c m.
    run_with_fuel n (q,r) = SOME (a,b,c) ∧
    run_with_fuel m (q,r) = SOME (x,y,c) ⇒
    n = m
Proof
  ho_match_mp_tac run_with_fuel_ind
  \\ rw[] \\ gs[run_with_fuel_def]
  \\ ntac 2 (pop_assum mp_tac)
  \\ rw[CaseEq"num"]
  \\ Cases_on`r` \\ gs[]
QED

Theorem run_n_with_fuel:
  ∀n q p s r t.
  (∀m. m < n ⇒ ISL (FST (run_n m s))) ∧ run_n n s = (INR r, t)
     ∧ s = SND (q, p) ∧ (ISL (FST (q, p))) ⇒
  run_with_fuel n (q, p) = SOME (r, t, 0)
Proof
  ho_match_mp_tac run_with_fuel_ind \\ rw[]
  \\ gs[run_n_def, run_with_fuel_def, CaseEq"bool", CaseEq"num"]
  \\ Cases_on`n` \\ gs[]
  \\ gs[FUNPOW]
  \\ Cases_on`step s` \\ gs[]
  \\ qmatch_assum_rename_tac`step s = (x,z)`
  \\ qmatch_asmsub_rename_tac`FUNPOW _ m`
  \\ Cases_on`m = 0` \\ gvs[]
  >- rw[run_with_fuel_def]
  \\ first_assum(qspec_then`SUC 0`mp_tac)
  \\ impl_tac >- simp[]
  \\ simp_tac (srw_ss()) [FUNPOW_SUC]
  \\ rw[] \\ gs[]
  \\ first_x_assum irule
  \\ Cases_on`x` \\ gs[]
  \\ qx_gen_tac`n` \\ strip_tac
  \\ first_x_assum(qspec_then`SUC n`mp_tac)
  \\ simp[FUNPOW]
QED

val () = cv_auto_trans process_deletions_def;

val post_transaction_accounting_pre_def = post_transaction_accounting_def
  |> cv_auto_trans_pre;

Theorem post_transaction_accounting_pre[cv_pre]:
  ∀blk tx result s t.
    post_transaction_accounting_pre blk tx result s t
Proof
  rw[post_transaction_accounting_pre_def]
  \\ strip_tac \\ gs[]
QED

val () = update_beacon_block_def |> cv_auto_trans;

val () = cv_auto_trans empty_return_destination_def;

val run_create_pre_def = run_create_def
  |> SIMP_RULE std_ss [o_DEF]
  |> cv_auto_trans_pre;

Theorem run_create_pre[cv_pre]:
  run_create_pre c p b a t
Proof
  rw[run_create_pre_def, initial_state_def]
QED

Definition run_transaction_with_fuel_def:
  run_transaction_with_fuel n chainId hs blk acc tx =
  case run_create chainId hs blk acc tx of
     | NONE => NONE
     | SOME (INL r) => SOME (r, n)
     | SOME (INR (a, s)) =>
         case run_with_fuel n (INL (), s) of
            | SOME (r, t, m) =>
                SOME $ (post_transaction_accounting blk tx r a t, m)
            | _ => NONE
End

val () = run_transaction_with_fuel_def |> cv_auto_trans;

Definition run_transactions_with_fuel_def:
  run_transactions_with_fuel n c h b a rs [] = SOME (rs, a, n) ∧
  run_transactions_with_fuel n c h b a rs (tx::txs) =
  case run_transaction_with_fuel n c h b a tx of
  | NONE => NONE
  | SOME ((r, a), n) => run_transactions_with_fuel n c h b a (r::rs) txs
End

val () = cv_auto_trans run_transactions_with_fuel_def;

Definition run_block_with_fuel_def:
  run_block_with_fuel n chainId h a b =
  OPTION_MAP (λ(rs, a, n). (REVERSE rs, a ,n)) $
  run_transactions_with_fuel n chainId h b (update_beacon_block b a) [] b.transactions
End

val () = cv_auto_trans run_block_with_fuel_def;

Theorem run_transaction_SOME_with_fuel:
  run_transaction c h b a tx = SOME p ⇔
  ∃n. run_transaction_with_fuel n c h b a tx = SOME (p, 0)
Proof
  rw[run_transaction_def, run_transaction_with_fuel_def]
  \\ reverse(rw[EQ_IMP_THM])
  \\ gvs[option_case_eq, pair_case_eq, CaseEq"sum", EXISTS_PROD]
  \\ gs[run_SOME_run_n]
  >- (
    drule run_with_fuel_to_zero
    \\ strip_tac
    \\ simp[PULL_EXISTS]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[] )
  \\ first_assum (mp_then (Pat`run_n`) mp_tac run_n_with_fuel)
  \\ simp[]
  \\ disch_then(qspec_then`INL ()`mp_tac)
  \\ simp[] \\ strip_tac
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem run_transactions_with_fuel_append:
  run_transactions_with_fuel n c h b a (rs ++ xs) ls =
  OPTION_MAP (λ(x,y,z). (x ++ xs,y,z)) $
  run_transactions_with_fuel n c h b a rs ls
Proof
  qid_spec_tac`rs`
  \\ qid_spec_tac`a`
  \\ qid_spec_tac`n`
  \\ Induct_on`ls`
  \\ rw[run_transactions_with_fuel_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ once_rewrite_tac[rich_listTheory.CONS_APPEND]
  \\ rewrite_tac[listTheory.APPEND_ASSOC]
  \\ simp[]
QED

Theorem run_transaction_with_fuel_add:
  run_transaction_with_fuel n c h b a t = SOME (x, m) ⇒
  run_transaction_with_fuel (n + d) c h b a t = SOME (x, m + d)
Proof
  rw[run_transaction_with_fuel_def, PULL_EXISTS, FORALL_PROD,
     CaseEq"option", CaseEq"sum", CaseEq"prod"]
  \\ drule run_with_fuel_add
  \\ disch_then(qspec_then`d`mp_tac)
  \\ simp[]
QED

Theorem run_transaction_with_fuel_sub:
  run_transaction_with_fuel n c h b a t = SOME (x, m) ⇒
  run_transaction_with_fuel (n - m) c h b a t = SOME (x, 0)
Proof
  rw[run_transaction_with_fuel_def, PULL_EXISTS, FORALL_PROD,
     CaseEq"option", CaseEq"sum", CaseEq"prod"]
  \\ drule run_with_fuel_sub
  \\ simp[]
QED

Theorem run_transaction_with_fuel_equal:
  run_transaction_with_fuel n c h b a t = SOME (x, m) ∧
  run_transaction_with_fuel p c h b a t = SOME (y, m)
  ⇒
  n = p
Proof
  rw[run_transaction_with_fuel_def, PULL_EXISTS, FORALL_PROD,
     CaseEq"option", CaseEq"sum", CaseEq"prod"] \\ gvs[]
  \\ drule_then irule run_with_fuel_equal
  \\ gs[]
QED

(* TODO: move? *)
Theorem FOLDL_OPTION_BIND_NONE:
  FOLDL (λx y. OPTION_BIND x (f x y)) NONE ls = NONE
Proof
  Induct_on`ls` \\ rw[]
QED
(* -- *)

Theorem run_block_SOME_with_fuel:
  run_block c h a b = SOME r ⇔
  ∃n. run_block_with_fuel n c h a b = SOME (FST r, SND r, 0)
Proof
  rw[run_block_def, run_block_with_fuel_def]
  \\ qspec_tac(`update_beacon_block b a`,`a`)
  \\ qid_spec_tac`r`
  \\ rewrite_tac[METIS_PROVE [REVERSE_DEF]
       ``run_transactions_with_fuel n c h b a [] =
         run_transactions_with_fuel n c h b a (REVERSE [])``]
  \\ qspec_tac(`[]:transaction_result list`,`rs`)
  \\ qspec_tac(`b.transactions`,`ls`)
  \\ Induct
  \\ gs[UNCURRY, FORALL_PROD, EXISTS_PROD, PULL_EXISTS]
  >- rw[run_transactions_with_fuel_def, EQ_IMP_THM]
  \\ rw[run_transactions_with_fuel_def]
  \\ qmatch_goalsub_rename_tac`run_transaction c h b a tx`
  \\ Cases_on`run_transaction c h b a tx` \\ gs[]
  \\ simp[FOLDL_OPTION_BIND_NONE]
  >- (
    rw[option_case_eq, pair_case_eq]
    \\ drule run_transaction_with_fuel_sub
    \\ strip_tac
    \\ metis_tac[run_transaction_SOME_with_fuel, NOT_SOME_NONE] )
  \\ gs[run_transaction_SOME_with_fuel]
  \\ PairCases_on`x` \\ gs[]
  \\ gs[option_case_eq, pair_case_eq, PULL_EXISTS, REVERSE_SNOC]
  \\ simp[EQ_IMP_THM, PULL_EXISTS]
  \\ conj_tac
  >- (
    qx_gen_tac`n1`
    \\ rpt strip_tac
    \\ drule run_transaction_with_fuel_add
    \\ disch_then(qspec_then`n1`mp_tac)
    \\ strip_tac
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gs[] )
  \\ qx_gen_tac`n1`
  \\ rpt strip_tac
  \\ drule run_transaction_with_fuel_sub
  \\ strip_tac
  \\ drule (Q.GENL[`p`,`y`]run_transaction_with_fuel_equal)
  \\ disch_then(qspec_then`n`mp_tac)
  \\ rw[] \\ gvs[]
  \\ metis_tac[]
QED

Definition run_block_to_hash_def:
  run_block_to_hash n1 n2 chainId prevHashes accounts blk =
  case run_block_with_fuel n1 chainId prevHashes accounts blk
    of NONE => NONE
     | SOME (rs, s, m) => SOME (m, state_root_clocked n2 s)
End

val () = cv_auto_trans run_block_to_hash_def;

val _ = export_theory();
