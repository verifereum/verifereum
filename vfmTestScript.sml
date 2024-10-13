open HolKernel boolLib bossLib Parse wordsLib dep_rewrite
     listTheory pairTheory optionTheory sumTheory
     arithmeticTheory combinTheory whileTheory
     vfmTypesTheory vfmExecutionTheory
     vfmStateTheory vfmContextTheory
     vfmOperationTheory vfmComputeTheory
     readTestJsonLib
     cv_transLib cv_stdTheory cv_computeLib
     cv_typeTheory cvTheory
     cv_primTheory byteTheory;

val _ = new_theory "vfmTest";

(* TODO: move/replace *)
Definition hex_to_bytes_def:
    hex_to_bytes [] = [] : byte list
  ∧ hex_to_bytes [c] = [n2w (UNHEX c)]
  ∧ hex_to_bytes (c1::c2::rest) =
      n2w (16 * UNHEX c1 + UNHEX c2)
      :: hex_to_bytes rest
End

val _ = cv_auto_trans hex_to_bytes_def;

(* cv_eval “hex_to_bytes "693c61390000000000000000000000000000000000000000000000000000000000000000"” *)

Theorem FOLDL_OPTION_BIND_NONE:
  FOLDL (λx y. OPTION_BIND x (f x y)) NONE ls = NONE
Proof
  Induct_on`ls` \\ rw[]
QED

fun cv_eval_match_tac pat =
  goal_term (fn tm =>
               let
                 val t = find_term (can (match_term pat)) tm
               in rewrite_tac [cv_eval t] end);

fun eval_match_tac pat =
  goal_term (fn tm =>
               let
                 val t = find_term (can (match_term pat)) tm
               in rewrite_tac [EVAL t] end);

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

val WHILE_FUNPOW = keccakTheory.WHILE_FUNPOW

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

(* TODO: move *)

val post_transaction_accounting_pre_def = post_transaction_accounting_def
  |> ONCE_REWRITE_RULE[GSYM lookup_account_def]
  |> ONCE_REWRITE_RULE[GSYM update_account_def]
  |> ONCE_REWRITE_RULE[GSYM update_account_def]
  |> cv_auto_trans_pre;

Theorem post_transaction_accounting_pre[cv_pre]:
  ∀blk tx result s t.
    post_transaction_accounting_pre blk tx result s t
Proof
  rw[post_transaction_accounting_pre_def]
  \\ strip_tac \\ gs[]
QED

val () = update_beacon_block_def
  |> ONCE_REWRITE_RULE[GSYM lookup_account_def]
  |> ONCE_REWRITE_RULE[GSYM update_storage_def]
  |> ONCE_REWRITE_RULE[GSYM update_account_def]
  |> cv_auto_trans;

val () = cv_auto_trans empty_return_destination_def;

(* -- *)

Definition run_transaction_with_fuel_def:
  run_transaction_with_fuel n chainId blk acc tx =
  OPTION_BIND
    (initial_state chainId acc blk empty_return_destination tx)
    (λs. OPTION_MAP
           (λ(r, t, m). (post_transaction_accounting blk tx r s.accounts t, m))
           (run_with_fuel n (INL (),
                             s with accounts updated_by
                             transfer_value tx.from tx.to tx.value)))
End

val () = cv_auto_trans run_transaction_with_fuel_def;

Definition run_transactions_with_fuel_def:
  run_transactions_with_fuel n c b a rs [] = SOME (rs, a, n) ∧
  run_transactions_with_fuel n c b a rs (tx::txs) =
  case run_transaction_with_fuel n c b a tx of
  | NONE => NONE
  | SOME ((r, a), n) => run_transactions_with_fuel n c b a (r::rs) txs
End

val () = cv_auto_trans run_transactions_with_fuel_def;

Definition run_block_with_fuel_def:
  run_block_with_fuel n chainId a b =
  OPTION_MAP (λ(rs, a, n). (REVERSE rs, a ,n)) $
  run_transactions_with_fuel n chainId b (update_beacon_block b a) [] b.transactions
End

val () = cv_auto_trans run_block_with_fuel_def;

Theorem run_transaction_SOME_with_fuel:
  run_transaction c b a tx = SOME p ⇔
  ∃n. run_transaction_with_fuel n c b a tx = SOME (p, 0)
Proof
  rw[run_transaction_def, run_transaction_with_fuel_def]
  \\ reverse(rw[EQ_IMP_THM])
  \\ gvs[option_case_eq, pair_case_eq, CaseEq"sum", EXISTS_PROD]
  \\ gs[run_SOME_run_n]
  >- (
    PairCases_on`z` \\ gvs[]
    \\ drule run_with_fuel_to_zero
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
  run_transactions_with_fuel n c b a (rs ++ xs) ls =
  OPTION_MAP (λ(x,y,z). (x ++ xs,y,z)) $
  run_transactions_with_fuel n c b a rs ls
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
  run_transaction_with_fuel n c b a t = SOME (x, m) ⇒
  run_transaction_with_fuel (n + d) c b a t = SOME (x, m + d)
Proof
  rw[run_transaction_with_fuel_def, PULL_EXISTS, FORALL_PROD]
  \\ drule run_with_fuel_add
  \\ disch_then(qspec_then`d`mp_tac)
  \\ simp[]
QED

Theorem run_transaction_with_fuel_sub:
  run_transaction_with_fuel n c b a t = SOME (x, m) ⇒
  run_transaction_with_fuel (n - m) c b a t = SOME (x, 0)
Proof
  rw[run_transaction_with_fuel_def, PULL_EXISTS, FORALL_PROD]
  \\ drule run_with_fuel_sub
  \\ simp[]
QED

Theorem run_transaction_with_fuel_equal:
  run_transaction_with_fuel n c b a t = SOME (x, m) ∧
  run_transaction_with_fuel p c b a t = SOME (y, m)
  ⇒
  n = p
Proof
  rw[run_transaction_with_fuel_def, PULL_EXISTS, FORALL_PROD]
  \\ drule_then irule run_with_fuel_equal
  \\ gs[]
QED

Theorem run_block_SOME_with_fuel:
  run_block c a b = SOME r ⇔
  ∃n. run_block_with_fuel n c a b = SOME (FST r, SND r, 0)
Proof
  rw[run_block_def, run_block_with_fuel_def]
  \\ qspec_tac(`update_beacon_block b a`,`a`)
  \\ qid_spec_tac`r`
  \\ rewrite_tac[METIS_PROVE [REVERSE_DEF]
       ``run_transactions_with_fuel n c b a [] =
         run_transactions_with_fuel n c b a (REVERSE [])``]
  \\ qspec_tac(`[]:transaction_result list`,`rs`)
  \\ qspec_tac(`b.transactions`,`ls`)
  \\ Induct
  \\ gs[UNCURRY, FORALL_PROD, EXISTS_PROD, PULL_EXISTS]
  >- rw[run_transactions_with_fuel_def, EQ_IMP_THM]
  \\ rw[run_transactions_with_fuel_def]
  \\ qmatch_goalsub_rename_tac`run_transaction c b a tx`
  \\ Cases_on`run_transaction c b a tx` \\ gs[]
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

val to_vfmExecution_transaction_result_def =
  theorem"to_vfmExecution_transaction_result_def";

(*
https://github.com/ethereum/tests
commit 08839f5 (taken from the develop branch)
BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json
*)

(*
  val (_, gt) = top_goal()
  Globals.max_print_depth := 12
*)
fun cv_eval_run_block_with_fuel_tac (goal as (_, gt)) = let
  val run_tm = find_term (can (match_term ``run_block_with_fuel _ _ _ _``)) gt
  val raw_th = cv_eval_raw run_tm
  val raw_th2 = raw_th |>
  REWRITE_RULE[
    cv_typeTheory.to_option_def,
    cv_typeTheory.to_pair_def,
    to_vfmExecution_transaction_result_def,
    cv_typeTheory.cv_has_shape_def,
    cvTheory.Num_11,
    EVAL``2n = 0``,
    EVAL``2n = 1``,
    EVAL``1n = 0``,
    to_evm_accounts_def,
    cv_typeTheory.to_list_def,
    cvTheory.cv_fst_def,
    cvTheory.cv_snd_def,
    cvTheory.c2n_def,
    to_vfmContext_execution_state_def,
    to_vfmContext_transaction_parameters_def,
    to_vfmContext_access_sets_def,
    to_vfmContext_context_def,
    to_vfmContext_call_parameters_def,
    to_vfmContext_return_destination_def,
    to_vfmContext_memory_range_def,
    to_evm_accounts_def,
    to_num_fset_def,
    to_word_fset_def,
    to_storage_key_fset_def,
    to_word_def,
    to_option_def,
    cv_has_shape_def,
    c2n_def, c2b_thm,
    to_list_def, cv_fst_def, cv_snd_def
  ]
in
  rewrite_tac[raw_th2]
end goal;

fun trim2 s = Substring.string(Substring.triml 2 (Substring.full s))

fun mk_statement test_name =
  Term[QUOTE(String.concat[
         "∃rs. run_block 1 ",
         test_name, "_pre ",
         test_name, "_block ",
         "= SOME (rs, ",
         test_name, "_post)"])]

val account_rwts = [
  account_state_component_equality,
  account_state_accessors,
  account_state_fn_updates,
  account_state_accfupds,
  empty_accounts_def, empty_account_state_def,
  empty_storage_def,
  K_THM, FUN_EQ_THM, APPLY_UPDATE_THM
];

(*
  set_goal([], thm_term)
  Globals.max_print_depth := 16
*)
fun mk_tactic num_steps =
  rw[run_block_SOME_with_fuel]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ exists_tac (numSyntax.term_of_int num_steps)
  \\ cv_eval_run_block_with_fuel_tac
  \\ simp[] \\ EVAL_TAC
  \\ rewrite_tac[FUN_EQ_THM] \\ gen_tac
  \\ rewrite_tac[APPLY_UPDATE_THM]
  \\ rpt ( IF_CASES_TAC >- (
       BasicProvers.VAR_EQ_TAC
       \\ simp_tac (std_ss ++ WORD_ss) []
       \\ rewrite_tac account_rwts
       \\ rpt gen_tac
       \\ rpt ( IF_CASES_TAC >- (
                  BasicProvers.VAR_EQ_TAC
                  \\ simp_tac (std_ss ++ WORD_ss) []
                ))
       \\ rewrite_tac[]))
  \\ simp_tac (std_ss ++ WORD_ss) []
  \\ rewrite_tac account_rwts

val run_block_with_fuel =
  run_block_with_fuel_def |> SPEC_ALL |> concl |> lhs
  |> strip_comb |> fst;

fun find_num_steps thm_term =
let
  val (_, args) = dest_exists thm_term |> snd |> lhs |> strip_comb
  fun loop n =
  let
    val n_tm = numSyntax.term_of_int n
    val run_tm = list_mk_comb(run_block_with_fuel, n_tm::args)
    val raw_th = cv_eval_raw run_tm
    val r_tm = raw_th |>
      REWRITE_RULE[to_option_def, to_pair_def, c2n_def] |>
      concl |> rhs
  in
    if optionSyntax.is_none r_tm
    then loop $ 2 * n
    else
      r_tm |> optionSyntax.dest_some |>
        pairSyntax.dest_pair |> snd |>
        pairSyntax.dest_pair |> snd |>
        numSyntax.int_of_term |>
        curry op - n
  end
  val n = 20
in
  loop n
end

fun accounts_term (ls:
   {address: string,
     balance: string,
     code: string, nonce: string, storage: {key: string, value: string} list}
   list) =
  List.foldl
    (fn (a, s) =>
      String.concat [
        "update_account (",
        s,
        ")(n2w ", #address a, ") <|",
        " nonce := ", #nonce a,
        ";balance := ", #balance a,
        ";code := hex_to_bytes \"", trim2 $ #code a,
        "\";storage := ",
        List.foldl
          (fn (e, s) =>
            String.concat [
              "update_storage (",
              s,
              ") (n2w ", #key e, ") (n2w ", #value e, ")"
            ])
            "empty_storage"
            (#storage a),
        "|>"
      ]) "empty_accounts" ls

(*
  val test_index = 0
*)
fun mk_prove_test test_path = let
  val test_names = get_test_names test_path;
  fun prove_test test_index = let
    val test_name = List.nth(test_names, test_index);
    val test = get_test test_path test_name;

    val transaction = #transaction test;
    val transaction_def = new_definition(
      test_name ^ "_transaction_def",
      Term[QUOTE(String.concat[
        test_name, "_transaction = <|",
        " from := n2w ", #sender transaction,
        ";to := n2w ", #to transaction,
        ";data := hex_to_bytes \"", trim2 $ #data transaction,
        "\";nonce := ", #nonce transaction,
        ";value := ", #value transaction,
        ";gasPrice := ", #gasPrice transaction,
        ";gasLimit := ", #gasLimit transaction,
        ";accessList := [] |>"
      ])]);

    val block = #block test;
    val block_def = new_definition(
      test_name ^ "_block_def",
      Term[QUOTE(String.concat[
        test_name, "_block = <|",
        " number := ", #number block,
        ";baseFeePerGas := ", #baseFeePerGas block,
        ";timeStamp := ", #timeStamp block,
        ";coinBase := n2w ", #coinBase block,
        ";hash := n2w ", #hash block,
        ";gasLimit := ", #gasLimit block,
        ";prevRandao := n2w ", #prevRandao block, (* TODO: not sure - using the difficulty *)
        ";parentBeaconBlockRoot := n2w ", #parentBeaconBlockRoot block,
        ";transactions := [", test_name, "_transaction]",
        "|>"
      ])]);

    val pre = #pre test;
    val pre_def = new_definition(
      test_name ^ "_pre_def",
      Term[QUOTE(test_name ^ "_pre = " ^ accounts_term pre)]);

    val post = #post test;
    val post_def = new_definition(
      test_name ^ "_post_def",
      Term[QUOTE(test_name ^ "_post = " ^ accounts_term post)]);

    val () = cv_auto_trans pre_def;
    val () = cv_auto_trans post_def;
    val () = cv_auto_trans transaction_def;
    val () = cv_auto_trans block_def;
    val () = computeLib.add_funs [pre_def, post_def, transaction_def, block_def]

    val thm_name = test_name ^ "_correctness";
    val thm_term = mk_statement test_name;

    val num_steps = find_num_steps thm_term
  in
    store_thm(thm_name, thm_term, mk_tactic num_steps)
  end
in (List.length test_names, prove_test) end

val test_path = "tests/add.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = "tests/iszero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = "tests/pc.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = "tests/slt.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = "tests/pop.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = "tests/jump.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests - 1, prove_test);
(* TODO: the last one fails - evm bug somewhere *)

val test_path = "tests/mload.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests - 2, prove_test);
(* TODO: some cv_eval problem in the 2nd one? *)

(*
* TODO: fix
val test_path = "tests/calldatacopy.json";
val (num_tests, prove_test) = mk_prove_test test_path;
*)

(*
TODO: does not work yet (fails out of gas), evm might have bugs
val test_path = "tests/loopExp.json";
val (num_tests, prove_test) = mk_prove_test test_path;
*)

(*

cv_eval ``
let acc = mload_d0g0v0_Cancun_pre in
let blk = mload_d0g0v0_Cancun_block in
let tx = mload_d0g0v0_Cancun_transaction in
let s = (THE $ initial_state 1 acc blk
               empty_return_destination tx) with accounts updated_by
           transfer_value tx.from tx.to tx.value in
let (r, s) = run_n 18 s in
let c = EL 0 s.contexts in
  (LENGTH s.contexts, c.stack, c.returnData, c.gasUsed,
   c.callParams.gasLimit, c.memory)
``

(79978796 - 26) - ((79978796 - 26) div 64)
val subLimit = 78726543
val usedBefore = 26
val parentUsed = 78729169
parentUsed - usedBefore - subLimit

cv_eval ``
let acc = pop_d1g0v0_Cancun_pre in
let blk = pop_d1g0v0_Cancun_block in
let tx = pop_d1g0v0_Cancun_transaction in
let (r, t, n) = THE $
  run_with_fuel 12 (INL (),
    (THE $
     initial_state 1 acc blk
       empty_return_destination
       tx) with accounts updated_by
           transfer_value tx.from tx.to tx.value) in
let c = HD t.contexts in
let sb1 = (lookup_account acc tx.from).balance in
let sb2 = (lookup_account t.accounts tx.from).balance in
  (r, n, tx.gasLimit, c.callParams.gasLimit,
   tx.gasPrice, blk.baseFeePerGas, c.stack,
   c.gasUsed, c.gasRefund, c.logs, c.returnData,
   tx.value,
   sb1 - sb2,
   sb1 - sb2 - (tx.gasLimit * tx.gasPrice)
   )
``

val txGasLimit = 80000000
val gasPrice = 10
val gasLimit = 79978808
val gasUsed = 7631
val refund = 4800
val gasLeft = gasLimit - gasUsed
val gasRefund = Int.min (gasUsed div 5, refund)
val refundEther = (gasLeft + gasRefund) * gasPrice
val totalGasUsed = gasUsed - gasRefund
val priorityFeePerGas = 0
val transactionFee = totalGasUsed * priorityFeePerGas

val discrepancy = 838137708090876753 - 838137708090664833
initial_state_def
post_transaction_accounting_def

val discrepancy = 17592185804185 - 17592185771445
val gas_discrepancy = discrepancy div gasPrice

discrepancy - gasLeft
cv_eval``intrinsic_cost pc_d0g0v0_Cancun_transaction.data``

cv_eval ``
let s =
(run_n 7 (THE (initial_state 1
    add_d1g0v0_Cancun_pre
    add_d1g0v0_Cancun_block
    (Memory <| offset := 0; size := 0 |>)
    add_d1g0v0_Cancun_transaction))) in
let c = EL 0 (SND s).contexts in
  (c.callParams.gasLimit, c.gasUsed, c.callParams.data, c.stack,
  c.callParams.outputTo, c.returnData)
``

cv_eval ``parse_opcode $ DROP 21 $
  (lookup_account
     add_d1g0v0_Cancun_pre
     add_d1g0v0_Cancun_transaction.to).code``

Push1 0
Push1 0
Push1 0
Push1 0
Push1 0
Push1 4
CallDataLoad
Push2 16 0
Add
Push3 255 255 255
Call

*)

val _ = export_theory();
