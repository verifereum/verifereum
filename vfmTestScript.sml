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

val run_block_with_fuel_pat =
  run_block_with_fuel_def |> SPEC_ALL |> concl |> lhs;

val run_block_with_fuel =
  run_block_with_fuel_pat |> strip_comb |> fst;

(*
  val (_, gt) = top_goal()
  Globals.max_print_depth := 12
*)
fun cv_eval_run_block_with_fuel_tac (goal as (_, gt)) = let
  val run_tm = find_term (can (match_term run_block_with_fuel_pat)) gt
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
         "∃rs. run_block 1 [] ", (* TODO: add prev hashes if needed *)
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

fun find_num_steps thm_term =
let
  val (_, args) = dest_exists thm_term |> snd |> lhs |> strip_comb
  val n = 14
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

fun mk_test_path s = "tests/BlockchainTests/GeneralStateTests/VMTests/" ^ s;

val test_path = mk_test_path "vmTests/calldatacopy.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmTests/calldataload.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmTests/calldatasize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmTests/dup.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmTests/push.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmTests/random.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmTests/swap.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/add.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/addmod.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/arith.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/div.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/divByZero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix
val test_path = mk_test_path "vmArithmeticTest/exp.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: fix
val test_path = mk_test_path "vmArithmeticTest/expPower2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "vmBitwiseLogicOperation/iszero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmBitwiseLogicOperation/slt.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/codecopy.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (1, prove_test);
(* TODO: same cv_eval problem as with mload? *)

val test_path = mk_test_path "vmIOandFlowOperations/pc.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/pop.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/jump.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/jumpi.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/mload.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (1, prove_test);
(* TODO: some cv_eval problem in the 2nd one? *)

val test_path = mk_test_path "vmIOandFlowOperations/sstore_sload.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(*
TODO: does not have explicit postStates so can't handle for now...
val test_path = mk_test_path "vmIOandFlowOperations/jumpToPush.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(*
TODO: does not work yet (fails out of gas), evm might have bugs
val test_path = mk_test_path "vmPerformance/loopExp.json";
val (num_tests, prove_test) = mk_prove_test test_path;
*)

(*

cv_eval ``
let acc = random_d5g0v0_Cancun_pre in
let blk = random_d5g0v0_Cancun_block in
let tx = random_d5g0v0_Cancun_transaction in
let s = (THE $ initial_state 1 acc blk
               empty_return_destination tx) with accounts updated_by
           transfer_value tx.from tx.to tx.value in
let (r, s) = run_n 14 s in
let c = EL 0 s.contexts in
  (LENGTH s.contexts, c.stack, c.returnData, c.gasUsed,
   c.callParams.gasLimit,
   c.pc,
   (*c.callParams.parsed,*)
   FLOOKUP c.callParams.parsed c.pc,
   (*DROP c.pc c.callParams.code, c.memory,*)
   (lookup_storage (lookup_account s.accounts c.callParams.callee).storage 0w)
   )
``

cv_eval ``random_d5g0v0_Cancun_block.number``

0x1005

0: Push1 0
2: Push1 0
4: Push1 0
6: Push1 0
8: Push1 0
10: Push1 4
12: CallDataLoad
13: Push2 16 0
16: Add
17: Gas
18: Call
19: Stop

*)

val _ = export_theory();
