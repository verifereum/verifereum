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

Theorem run_transactions_with_fuel_sub:
  !ts n a rs qs m j.
  run_transactions_with_fuel n c h b a rs ts = SOME (qs,d,m) /\ j <= m ==>
  m ≤ n ∧
  run_transactions_with_fuel (n - j) c h b a rs ts = SOME (qs,d,m - j)
Proof
  Induct
  \\ simp[run_transactions_with_fuel_def]
  \\ qx_gen_tac`x` \\ rpt gen_tac
  \\ gvs[CaseEq"option", CaseEq"prod", PULL_EXISTS]
  \\ qx_genl_tac[`p`,`f`,`e`] \\ strip_tac
  \\ first_x_assum drule
  \\ disch_then(fn th => assume_tac th \\ qspec_then`0`mp_tac th)
  \\ impl_tac \\ simp[] \\ strip_tac
  \\ drule run_transaction_with_fuel_sub
  \\ strip_tac
  \\ drule run_transaction_with_fuel_add
  \\ disch_then(qspec_then`p - j`mp_tac)
  \\ simp[]
  \\ `p ≤ n`
  by (
    CCONTR_TAC
    \\ qhdtm_x_assum`run_transaction_with_fuel`mp_tac
    \\ qhdtm_x_assum`run_transaction_with_fuel`mp_tac
    \\ simp[run_transaction_with_fuel_def, run_with_fuel_def,
            run_create_def, CaseEq"bool", CaseEq"num", PULL_EXISTS,
            CaseEq"option", CaseEq"sum", CaseEq"prod"]
    \\ rpt gen_tac
    \\ strip_tac \\ gvs[]
    \\ qmatch_asmsub_abbrev_tac`run_with_fuel _ pp`
    \\ Cases_on`pp`
    \\ drule run_with_fuel_sub
    \\ gs[run_with_fuel_def, CaseEq"bool", CaseEq"num"]
    \\ strip_tac \\ gvs[]
    \\ metis_tac[NOT_ISL_ISR])
  \\ simp[]
QED

Theorem run_block_with_fuel_sub:
  run_block_with_fuel n c h a b = SOME (x, y, m) ==>
  run_block_with_fuel (n - m) c h a b = SOME (x, y, 0)
Proof
  rw[run_block_with_fuel_def, EXISTS_PROD]
  \\ drule run_transactions_with_fuel_sub
  \\ disch_then(qspec_then`m`mp_tac)
  \\ simp[]
QED

Theorem run_block_with_fuel_cv_sub:
  run_block_with_fuel n c h a b =
  to_option (to_pair f (to_pair g cv$c2n))
    (Pair (Num z) (Pair x (Pair y (Num m))))
  ⇒
  run_block_with_fuel (n - m) c h a b =
  to_option (to_pair f (to_pair g cv$c2n))
    (Pair (Num z) (Pair x (Pair y (Num 0))))
Proof
  rw[to_option_def, to_pair_def]
  \\ irule run_block_with_fuel_sub
  \\ rw[]
QED

val run_block_with_fuel_pat =
  run_block_with_fuel_def |> SPEC_ALL |> concl |> lhs;

val run_block_with_fuel =
  run_block_with_fuel_pat |> strip_comb |> fst;

val cv_eval_run_block_with_fuel_rwts = [
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
];

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
*)
fun mk_tactic num_steps eval_th =
  rw[run_block_SOME_with_fuel]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ exists_tac num_steps
  \\ rewrite_tac[eval_th]
  \\ rewrite_tac cv_eval_run_block_with_fuel_rwts
  \\ rewrite_tac[LET_THM]
  \\ CONV_TAC(PATH_CONV"blrrrlr"(BETA_CONV THENC EVAL))
  \\ rewrite_tac[SOME_11, PAIR_EQ]
  \\ Ho_Rewrite.REWRITE_TAC[UNWIND_THM1]
  \\ rewrite_tac[FUN_EQ_THM] \\ gen_tac
  \\ rewrite_tac[APPLY_UPDATE_THM]
  \\ CONV_TAC(RAND_CONV EVAL)
  \\ rpt (
     IF_CASES_TAC >- (
       BasicProvers.VAR_EQ_TAC
       \\ simp_tac (std_ss ++ WORD_ss) []
       \\ rewrite_tac account_rwts
       \\ rpt gen_tac
       \\ rpt (
          IF_CASES_TAC >- (
            BasicProvers.VAR_EQ_TAC
            \\ CONV_TAC(DEPTH_CONV word_EQ_CONV)
            \\ rewrite_tac[]
          ))
       \\ rewrite_tac[]
    ))
  \\ rewrite_tac account_rwts

fun find_num_steps thm_term =
let
  val (_, args) = dest_exists thm_term |> snd |> lhs |> strip_comb
  val name = last args |> dest_const |> fst
  fun msg pre n = pre ^ " num steps " ^ Int.toString n ^ " for " ^ name ^ "\n"
  val n = 65536
  fun loop n =
  let
    val () = TextIO.print $ msg "Trying" n
    val n_tm = numSyntax.term_of_int n
    val run_tm = list_mk_comb(run_block_with_fuel, n_tm::args)
    val raw_th = cv_eval_raw run_tm
    val r_tm = raw_th |>
      REWRITE_RULE[to_option_def, to_pair_def, c2n_def] |>
      concl |> rhs
  in
    if optionSyntax.is_none r_tm
    then loop $ 2 * n
    else (raw_th, n)
  end
  val (raw_th, n) = loop n
  val zero_th = MATCH_MP run_block_with_fuel_cv_sub raw_th
                |> CONV_RULE (PATH_CONV "lrllllr" numLib.REDUCE_CONV)
  val num_steps = zero_th |> concl |> lhs |> strip_comb |>
                  #2 |> el 1
  val () = TextIO.print $ msg "Found" $ numSyntax.int_of_term num_steps
in
  (num_steps, zero_th)
end

type account = {
  address: string, balance: string, code: string,
  nonce: string, storage: {key: string, value: string} list
};

val max_inline_code_size = 128;

val codeCache: (string, string) Redblackmap.dict ref =
  ref $ Redblackmap.mkDict String.compare;

fun mk_code_syntax code =
  "REVERSE $ hex_to_rev_bytes [] \"" ^ trim2 code ^ "\"";

fun accounts_term (ls: account list) =
  List.foldl
    (fn (a, s) =>
      String.concat [
        "update_account (n2w ", #address a, ") <|",
        " nonce := ", #nonce a,
        ";balance := ", #balance a,
        ";code := ", case Redblackmap.peek(!codeCache, #code a) of
                          NONE => mk_code_syntax $ #code a
                        | SOME name => name,
        ";storage := ",
        List.foldl
          (fn (e, s) =>
            String.concat [
              "update_storage (n2w ", #key e,
              ") (n2w ", #value e, ") (", s, ")"
            ])
            "empty_storage"
            (#storage a),
        "|> (", s, ")"
      ]) "empty_accounts" ls

fun mk_code_name prefix address =
  prefix ^ address  ^ "_code";

fun mk_code_def prefix (a: account) =
let
  val code = #code a
in
  if Redblackmap.inDomain(!codeCache, code) then NONE else
  if String.size code <= max_inline_code_size then NONE else
  let
    val address = #address a
    val code_name = mk_code_name prefix address
    val defn = Term[QUOTE(String.concat[code_name, " = ", mk_code_syntax code])]
    val thm = new_definition(code_name ^ "_def", defn)
    val () = codeCache := Redblackmap.insert(!codeCache, code, code_name)
  in
    SOME thm
  end
end

fun mk_code_defs prefix acc (ls: account list) =
  List.foldl
    (fn (a, l) =>
      case mk_code_def prefix a
        of NONE => l
         | SOME def => def::l) acc ls

fun mk_tx_to s =
  if String.size s = 0 then "NONE"
  else "SOME (n2w " ^ s ^ ")"

(*
  val test_index = 0;
  Globals.max_print_depth := 32;
  val json_path = test_path
*)
fun mk_prove_test test_path = let
  val test_names = get_test_names test_path;
  fun prove_test test_index = let
    val test_name = List.nth(test_names, test_index);
    val test_name_escaped =
      String.translate(fn c => if c = #"-" then "_" else String.str c) test_name

    val test = get_test test_path test_name;

    val transaction = #transaction test;
    val transaction_def = new_definition(
      test_name_escaped ^ "_transaction_def",
      Term[QUOTE(String.concat[
        test_name_escaped, "_transaction = <|",
        " from := n2w ", #sender transaction,
        ";to := ", mk_tx_to (#to transaction),
        ";data := REVERSE $ hex_to_rev_bytes [] \"", trim2 $ #data transaction,
        "\";nonce := ", #nonce transaction,
        ";value := ", #value transaction,
        ";gasPrice := ", #gasPrice transaction,
        ";gasLimit := ", #gasLimit transaction,
        ";accessList := [] |>"
      ])]);

    val block = #block test;
    val block_def = new_definition(
      test_name_escaped ^ "_block_def",
      Term[QUOTE(String.concat[
        test_name_escaped, "_block = <|",
        " number := ", #number block,
        ";baseFeePerGas := ", #baseFeePerGas block,
        ";timeStamp := ", #timeStamp block,
        ";coinBase := n2w ", #coinBase block,
        ";hash := n2w ", #hash block,
        ";gasLimit := ", #gasLimit block,
        ";prevRandao := n2w ", #prevRandao block,
        ";parentBeaconBlockRoot := n2w ", #parentBeaconBlockRoot block,
        ";transactions := [", test_name_escaped, "_transaction]",
        "|>"
      ])]);

    val pre = #pre test;
    val pre_name = test_name_escaped ^ "_pre";
    val pre_prefix = pre_name ^ "_";
    val code_defs = mk_code_defs pre_prefix [] pre;
    val pre_def = new_definition(pre_name ^ "_def",
      Term[QUOTE(pre_name ^ " = " ^ accounts_term pre)]);

    val post = #post test;
    val post_name = test_name_escaped ^ "_post";
    val post_prefix = post_name ^ "_";
    val code_defs = mk_code_defs post_prefix code_defs post;
    val post_def = new_definition(post_name ^ "_def",
      Term[QUOTE(post_name ^ " = " ^ accounts_term post)]);

    val () = List.app (cv_trans_deep_embedding EVAL) code_defs;
    val () = cv_auto_trans pre_def;
    val () = cv_auto_trans post_def;
    val () = cv_auto_trans transaction_def;
    val () = cv_auto_trans block_def;
    val () = computeLib.add_funs [pre_def, post_def, transaction_def, block_def]
    val () = computeLib.add_funs code_defs;

    val thm_name = test_name_escaped ^ "_correctness";
    val thm_term = mk_statement test_name_escaped;

    val (num_steps, eval_th) = find_num_steps thm_term
  in
    store_thm(thm_name, thm_term, mk_tactic num_steps eval_th)
  end
in (List.length test_names, prove_test) end

fun mk_test_path s = "tests/BlockchainTests/GeneralStateTests/VMTests/" ^ s;

val test_path = mk_test_path "vmTests/blockInfo.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

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

val test_path = mk_test_path "vmTests/envInfo.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmTests/push.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmTests/random.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: cv_eval oom in d3g0v0 *)
val test_path = mk_test_path "vmTests/sha3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmTests/suicide.json";
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

val test_path = mk_test_path "vmArithmeticTest/exp.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/expPower2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/expPower256.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/expPower256Of256.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/fib.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/mod.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/mul.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/mulmod.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/not.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/sdiv.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/signextend.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/smod.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmArithmeticTest/sub.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: cv_eval oom problem? *)
val test_path = mk_test_path "vmArithmeticTest/twoOps.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmBitwiseLogicOperation/and.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmBitwiseLogicOperation/byte.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmBitwiseLogicOperation/eq.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmBitwiseLogicOperation/gt.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmBitwiseLogicOperation/iszero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmBitwiseLogicOperation/sgt.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmBitwiseLogicOperation/slt.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmBitwiseLogicOperation/xor.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/codecopy.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/gas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/jump.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(*
TODO: does not have explicit postStates so can't handle for now...
val test_path = mk_test_path "vmIOandFlowOperations/jumpToPush.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "vmIOandFlowOperations/jumpi.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/loop_stacklimit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/loopsConditionals.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/mload.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/msize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/mstore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/mstore8.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/pc.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/pop.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/return.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmIOandFlowOperations/sstore_sload.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: add log tests - may need to check logs in theorem statement *)

(* TODO: cv_eval oom problem? *)
val test_path = mk_test_path "vmPerformance/loopExp.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: very long test... find the num_steps manually to avoid excessive runs *)
val test_path = mk_test_path "vmPerformance/loopMul.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmPerformance/performanceTester.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stArgsZeroOneBalance/" ^ s;

val test_path = mk_test_path "addNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "addmodNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "andNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "balanceNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "byteNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (1, prove_test);
(*
* TODO: needs precompile ecRecover
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "callcodeNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (1, prove_test);
(*
* TODO: needs precompile ecRecover
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "calldatacopyNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "calldataloadNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "codecopyNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecallNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (1, prove_test);
(*
* TODO: needs precompile ecRecover
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "divNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "eqNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "expNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extcodecopyNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extcodesizeNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "gtNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "iszeroNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "jumpNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "jumpiNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO support logs
log0NonConst.json
log1NonConst.json
log2NonConst.json
log3NonConst.json
*)

val test_path = mk_test_path "ltNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mloadNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "modNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mstore8NonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mstoreNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mulNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mulmodNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "notNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "orNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returnNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sdivNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sgtNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sha3NonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "signextNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sloadNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sltNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "smodNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstoreNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "subNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "suicideNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "xorNonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stAttackTest/" ^ s;

(* TODO: long test, find num steps manually?
val test_path = mk_test_path "ContractCreationSpam.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: too slow
val test_path = mk_test_path "CrashingTransaction.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stBadOpcode/" ^ s;

val test_path = mk_test_path "eip2315NotRemoved.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: needs precompiles
val test_path = mk_test_path "invalidAddr.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "invalidDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: too slow from d9g0v0
val test_path = mk_test_path "measureGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "opc0CDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc0DDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc0EDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc0FDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc1EDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc1FDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc21DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc22DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc23DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc24DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc25DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc26DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc27DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc28DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc29DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc2ADiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc2BDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc2CDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc2DDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc2EDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc2FDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc49DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc4ADiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc4BDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc4CDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc4DDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc4EDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc4FDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc5CDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc5DDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc5EDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opc5FDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcA5DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcA6DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcA7DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcA8DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcA9DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcAADiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcABDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcACDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcADDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcAEDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcAFDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcB0DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcB1DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcB2DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcB3DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcB4DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcB5DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcB6DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcB7DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcB8DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcB9DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcBADiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcBBDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcBCDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcBDDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcBEDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcBFDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcC0DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcC1DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcC2DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcC3DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcC4DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcC5DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcC6DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcC7DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcC8DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcC9DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcCADiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcCBDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcCCDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcCDDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcCEDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcCFDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcD0DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcD1DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcD2DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcD3DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcD4DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcD5DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcD6DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcD7DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcD8DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcD9DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcDADiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcDBDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcDCDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcDDDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcDEDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcDFDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcE0DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcE1DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcE2DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcE3DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcE4DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcE5DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcE6DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcE7DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcE8DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcE9DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcEADiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcEBDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcECDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcEDDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcEEDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcEFDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcF6DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcF7DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcF8DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcF9DiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcFBDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcFCDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "opcFEDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow
val test_path = mk_test_path "operationDiffGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: no explicit postStates
val test_path = mk_test_path "undefinedOpcodeFirstByte.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

fun mk_test_path s = "tests/BlockchainTests/GeneralStateTests/stBugs/" ^ s;

val test_path = mk_test_path "randomStatetestDEFAULT-Tue_07_58_41-15153-575192.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
"randomStatetestDEFAULT-Tue_07_58_41-15153-575192_london.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopyPythonBug_Tue_03_48_41-1432.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "staticcall_createfails.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s = "tests/BlockchainTests/GeneralStateTests/stCallCodes/" ^ s;

val test_path = mk_test_path "call_OOG_additionalGasCosts1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "call_OOG_additionalGasCosts2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcall_00.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcall_00_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcall_00_OOGE_valueTransfer.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcall_00_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcall_000.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcall_000_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcall_000_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcall_000_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcall_000_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcall_000_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcode_01.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcode_01_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcode_01_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeDynamicCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeDynamicCode2SelfCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeEmptycontract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeInInitcodeToEmptyContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "callcodeInInitcodeToExisContractWithVTransferNEMoney.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeInInitcodeToExistingContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "callcodeInInitcodeToExistingContractWithValueTransfer.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcode_checkPC.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecall_10.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecall_10_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecall_10_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcode_11.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcode_11_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcode_11_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stCallCreateCallCodeTest/" ^ s;

val test_path = mk_test_path "Call1024BalanceTooLow.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Call1024OOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Call1024PreCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallLoseGasOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallRecursiveBombPreCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Callcode1024BalanceTooLow.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Callcode1024OOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallcodeLoseGasOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callOutput1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callOutput2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callOutput3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callOutput3Fail.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callOutput3partial.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callOutput3partialFail.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callWithHighValue.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callWithHighValueAndGasOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callWithHighValueAndOOGatTxLevel.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callWithHighValueOOGinCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeOutput1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeOutput2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeOutput3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeOutput3Fail.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeOutput3partial.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeOutput3partialFail.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeWithHighValue.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeWithHighValueAndGasOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "contractCreationMakeCallThatAskMoreGasThenTransactionProvided.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createFailBalanceTooLow.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createInitFailBadJumpDestination.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createInitFailBadJumpDestination2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createInitFailStackSizeLargerThan1024.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createInitFailStackUnderflow.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createInitFailUndefinedInstruction.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createInitFailUndefinedInstruction2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createInitFail_OOGduringInit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createInitFail_OOGduringInit2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createInitOOGforCREATE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createJS_ExampleContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createJS_NoCollision.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistratorPerTxs.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistratorPerTxsNotEnoughGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistratorPreStore1NotEnoughGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistratorendowmentTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stCallDelegateCodesCallCodeHomestead/" ^ s;

val test_path = mk_test_path "callcallcallcode_001.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcode_01.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcode_01_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcode_01_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecall_10.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecall_10_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecall_10_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcode_11.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcode_11_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcode_11_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stCallDelegateCodesHomestead/" ^ s;

val test_path = mk_test_path "callcallcallcode_001.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_001_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcode_01.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcode_01_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcode_01_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_010_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_011_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcodecallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecall_10.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecall_10_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecall_10_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_100_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_101_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcode_11.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcode_11_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcode_11_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_110_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_OOGMAfter.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_OOGMBefore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_111_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodecallcodecallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stChainId/" ^ s;

val test_path = mk_test_path "chainId.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "chainIdGasCost.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stCodeCopyTest/" ^ s;

val test_path = mk_test_path "ExtCodeCopyTargetRangeLongerThanCodeTests.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ExtCodeCopyTestsParis.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);


(* Precompile tests *)
fun mk_test_path s = "tests/BlockchainTests/GeneralStateTests/stPreCompiledContracts/" ^ s;

(* val test_path = mk_test_path "idPrecomps.json"; *)
(* val (num_tests, prove_test) = mk_prove_test test_path; *)
(* val thms = List.tabulate (num_tests, prove_test); *)

val test_path = mk_test_path "identity_to_smaller.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "identity_to_bigger.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);


fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stCodeSizeLimit/" ^ s;

val test_path = mk_test_path "codesizeInit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "codesizeOOGInvalidSize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "codesizeValid.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2CodeSizeLimit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createCodeSizeLimit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stCreate2/" ^ s;

val test_path = mk_test_path "CREATE2_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE2_Bounds2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE2_Bounds3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "CREATE2_ContractSuicideDuringInit_ThenStoreThenReturn.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: no postStates
val test_path = mk_test_path "CREATE2_FirstByte_loop.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "CREATE2_HighNonce.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE2_HighNonceDelegatecall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE2_HighNonceMinus1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE2_Suicide.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create2OOGFromCallRefunds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create2OOGafterInitCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create2OOGafterInitCodeReturndata.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create2OOGafterInitCodeReturndata2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create2OOGafterInitCodeReturndata3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create2OOGafterInitCodeReturndataSize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create2OOGafterInitCodeRevert.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create2OOGafterInitCodeRevert2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create2OnDepth1023.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create2OnDepth1024.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix json parse
val test_path = mk_test_path "Create2Recursive.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "CreateMessageReverted.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateMessageRevertedOOGInInit2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertDepthCreate2OOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertDepthCreate2OOGBerlin.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertDepthCreateAddressCollision.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertDepthCreateAddressCollisionBerlin.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix
val test_path = mk_test_path "RevertInCreateInInitCreate2Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "RevertOpcodeCreate.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOpcodeInCreateReturnsCreate2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "call_outsize_then_create2_successful_then_returndatasize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "call_then_create2_successful_then_returndatasize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2InitCodes.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2SmartInitCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix
val test_path = mk_test_path "create2callPrecompiles.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "create2checkFieldsInInitcode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2collisionBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2collisionCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2collisionCode2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2collisionNonce.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2collisionSelfdestructed.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2collisionSelfdestructed2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2collisionSelfdestructedOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2collisionSelfdestructedRevert.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2collisionStorageParis.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create2noCash.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_0_0_following_successful_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_afterFailing_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_following_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_following_revert_in_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_following_successful_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_following_successful_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stCreateTest/" ^ s;

val test_path = mk_test_path "CREATE2_CallData.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE2_RefundEF.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_AcreateB_BSuicide_BStore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_ContractRETURNBigOffset.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_ContractSSTOREDuringInit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_ContractSuicideDuringInit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "CREATE_ContractSuicideDuringInit_ThenStoreThenReturn.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_ContractSuicideDuringInit_WithValue.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_ContractSuicideDuringInit_WithValueToItself.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_EContractCreateEContractInInit_Tr.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_EContractCreateNEContractInInitOOG_Tr.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_EContractCreateNEContractInInit_Tr.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_EContract_ThenCALLToNonExistentAcc.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_EmptyContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_EmptyContractAndCallIt_0wei.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_EmptyContractAndCallIt_1wei.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_EmptyContractWithBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_EmptyContractWithStorage.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_EmptyContractWithStorageAndCallIt_0wei.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_EmptyContractWithStorageAndCallIt_1wei.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix parse
val test_path = mk_test_path "CREATE_FirstByte_loop.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "CREATE_HighNonce.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_HighNonceMinus1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_empty000CreateinInitCode_Transaction.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CodeInConstructor.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateAddressWarmAfterFail.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateCollisionResults.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateCollisionToEmpty2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateOOGFromCallRefunds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateOOGFromEOARefunds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateOOGafterInitCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateOOGafterInitCodeReturndata.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateOOGafterInitCodeReturndata2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateOOGafterInitCodeReturndata3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateOOGafterInitCodeReturndataSize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateOOGafterInitCodeRevert.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateOOGafterInitCodeRevert2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow *)
val test_path = mk_test_path "CreateOOGafterMaxCodesize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateResults.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateTransactionCallData.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix parse
val test_path = mk_test_path "CreateTransactionHighNonce.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "CreateTransactionRefundEF.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TransactionCollisionToEmpty2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TransactionCollisionToEmptyButCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TransactionCollisionToEmptyButNonce.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createFailResult.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow *)
val test_path = mk_test_path "createLargeResult.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stDelegatecallTestHomestead/" ^ s;

val test_path = mk_test_path "Call1024BalanceTooLow.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Call1024OOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Call1024PreCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallLoseGasOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallRecursiveBombPreCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallcodeLoseGasOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Delegatecall1024.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Delegatecall1024OOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callOutput1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callOutput2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callOutput3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callOutput3partial.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callOutput3partialFail.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callWithHighValueAndGasOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeOutput3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeWithHighValueAndGasOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "deleagateCallAfterValueTransfer.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecallAndOOGatTxLevel.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecallBasic.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecallEmptycontract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecallInInitcodeToEmptyContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecallInInitcodeToExistingContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecallInInitcodeToExistingContractOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecallOOGinCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecallSenderCheck.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecallValueCheck.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecodeDynamicCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "delegatecodeDynamicCode2SelfCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stEIP150Specific/" ^ s;

val test_path = mk_test_path "CallAndCallcodeConsumeMoreGasThenTransactionHas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallAskMoreGasOnDepth2ThenTransactionHas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallGoesOOGOnSecondLevel.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallGoesOOGOnSecondLevel2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateAndGasInsideCreate.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "DelegateCallOnEIP.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ExecuteCallThatAskForeGasThenTrabsactionHas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NewGasPriceForCodes.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "SuicideToExistingContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "SuicideToNotExistingContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Transaction64Rule_d64e0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Transaction64Rule_d64m1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Transaction64Rule_d64p1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Transaction64Rule_integerBoundaries.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stEIP150singleCodeGasPrices/" ^ s;

val test_path = mk_test_path "RawBalanceGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallCodeGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallCodeGasAsk.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallCodeGasMemory.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallCodeGasMemoryAsk.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallCodeGasValueTransfer.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallCodeGasValueTransferAsk.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallCodeGasValueTransferMemory.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallCodeGasValueTransferMemoryAsk.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallGasAsk.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallGasValueTransfer.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallGasValueTransferAsk.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallGasValueTransferMemory.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallGasValueTransferMemoryAsk.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallMemoryGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCallMemoryGasAsk.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCreateFailGasValueTransfer.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCreateFailGasValueTransfer2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCreateGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCreateGasMemory.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCreateGasValueTransfer.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawCreateGasValueTransferMemory.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawDelegateCallGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawDelegateCallGasAsk.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawDelegateCallGasMemory.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawDelegateCallGasMemoryAsk.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawExtCodeCopyGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawExtCodeCopyMemoryGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RawExtCodeSizeGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "eip2929-ff.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "eip2929.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "eip2929OOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "gasCost.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "gasCostBerlin.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "gasCostExp.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "gasCostJump.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "gasCostMemSeg.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "gasCostMemory.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "gasCostReturn.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s = "tests/BlockchainTests/GeneralStateTests/stEIP1559/" ^ s;

val test_path = mk_test_path "baseFeeDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "gasPriceDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: parse error
val test_path = mk_test_path "intrinsic.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse error
val test_path = mk_test_path "lowFeeCap.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse error
val test_path = mk_test_path "lowGasLimit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse error
val test_path = mk_test_path "lowGasPriceOldTypes.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse error
val test_path = mk_test_path "outOfFunds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse error
val test_path = mk_test_path "outOfFundsOldTypes.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse error
val test_path = mk_test_path "senderBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse error
val test_path = mk_test_path "tipTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse error
val test_path = mk_test_path "transactionIntinsicBug_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse error
val test_path = mk_test_path "typeTwoBerlin.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse error
val test_path = mk_test_path "valCausesOOF.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stEIP158Specific/" ^ s;

val test_path = mk_test_path "CALL_OneVCallSuicide.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CALL_OneVCallSuicide2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CALL_ZeroVCallSuicide.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "EXP_Empty.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "EXTCODESIZE_toEpmtyParis.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "EXTCODESIZE_toNonExistent.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callToEmptyThenCallErrorParis.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vitalikTransactionTestParis.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stEIP2930/" ^ s;

(* TODO: need accessList
val test_path = mk_test_path "addressOpcodes.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: fix
val test_path = mk_test_path "coinbaseT01.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse
val test_path = mk_test_path "coinbaseT2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: accessList
val test_path = mk_test_path "manualCreate.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: accessList
val test_path = mk_test_path "storageCosts.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: accessList
val test_path = mk_test_path "transactionCosts.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: accessList
val test_path = mk_test_path "variedContext.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stEIP3607/" ^ s;

val test_path = mk_test_path "initCollidingWithNonEmptyAccount.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: parse
val test_path = mk_test_path
  "transactionCollidingWithNonEmptyAccount_calls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse
val test_path = mk_test_path
  "transactionCollidingWithNonEmptyAccount_callsItself.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse
val test_path = mk_test_path
  "transactionCollidingWithNonEmptyAccount_init_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse
val test_path = mk_test_path
  "transactionCollidingWithNonEmptyAccount_send_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stExample/" ^ s;

(* TODO: accessList
val test_path = mk_test_path "accessListExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "add11.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "add11_yml.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: parse
val test_path = mk_test_path "basefeeExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse
val test_path = mk_test_path "eip1559.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "indexesOmitExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: parse
val test_path = mk_test_path "invalidTr.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "labelsExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: parse
val test_path = mk_test_path "mergeTest.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "rangesExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "solidityExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "yulExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(*

cv_eval ``
let acc = codesizeInit_d0g0v0_Cancun_pre in
let blk = codesizeInit_d0g0v0_Cancun_block in
let tx = codesizeInit_d0g0v0_Cancun_transaction in
let init = run_create 1 [] blk acc tx in
let cont = OUTR $ THE init in
let s = SND cont in
let (r, s) = run_n 7 s in
let c = EL 0 s.contexts in
  (ISL r, LENGTH s.contexts,
   c.stack,
   c.callParams.data,
   c.returnData,
   c.gasUsed,
   c.callParams.gasLimit,
   c.gasRefund,
   (*
   (EL 1 s.contexts).gasUsed,
   *)
   c.jumpDest,
   (*
   word_of_bytes F (0w:bytes32) $ REVERSE (lookup_account s.accounts 0xc0dew).code,
   *)
   (*
   [fIN 4096w c.callParams.accesses.addresses;
    fIN 4097w c.callParams.accesses.addresses;
    fIN 0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCw
    c.callParams.accesses.addresses;
   ],
   *)
   (*c.callParams.parsed,*)
   FLOOKUP c.callParams.parsed c.pc,
   (*DROP c.pc c.callParams.code,*) LENGTH c.memory,
   c.memory,
   c.callParams.static,
   c.callParams.callee,
   (lookup_account c.callParams.callee s.accounts).balance,
   (lookup_storage 0w (lookup_account c.callParams.callee s.accounts).storage),
   (lookup_storage 1w (lookup_account c.callParams.callee s.accounts).storage)
   (*
   (lookup_account 0x1007w s.accounts).balance
   (lookup_storage (lookup_account s.accounts 0x100fw).storage 0w),
   (lookup_storage (lookup_account s.accounts c.callParams.callee).storage 1w),
   (lookup_storage (lookup_account s.accounts c.callParams.callee).storage 2w),
   (lookup_storage (lookup_account s.accounts c.callParams.callee).storage 256w)
   *)
   )
``

TypeBase.fields_of``:execution_state`` |> map (fn x => (fst x, #ty $ snd x))
TypeBase.fields_of``:access_sets`` |> map (fn x => (fst x, #ty $ snd x))
TypeBase.fields_of``:transaction_parameters`` |> map (fn x => (fst x, #ty $ snd x))
TypeBase.fields_of``:context`` |> map (fn x => (fst x, #ty $ snd x))
TypeBase.fields_of``:call_parameters`` |> map (fn x => (fst x, #ty $ snd x))

Theorem fEMPTY_word_cv_rep[cv_rep]:
  from_word_fset fEMPTY = Num 0
Proof
  rw[from_word_fset_def, fEMPTY_num_cv_rep]
QED

cv_eval
``
let ea = <| addresses := fEMPTY; storageKeys := fEMPTY |> in
let cp = <|
         caller := 0w;
         callee := 0w;
         code := [];
         parsed := FEMPTY;
         value := 0;
         static := F;
         gasLimit := 0;
         data := [];
         outputTo := empty_return_destination;
         accounts := empty_accounts;
         accesses := ea |> in
let c = <|
  stack := [0x10000000000000001w; 32768w];
       memory := [];
       pc := 0;
       jumpDest := NONE;
       returnData := [];
       gasUsed := 0;
       gasRefund := 0;
       logs := [];
       callParams := cp |> in
let (x, y) =  step_inst SignExtend
  <| contexts := [ c; c ]
   ; txParams := <| origin := 0w; gasPrice := 0; baseFeePerGas := 0;
                    blockNumber := 0; blockTimeStamp := 0;
                    blockCoinBase := 0w; blockGasLimit := 0;
                    prevRandao := 0w; prevHashes := []; chainId := 0 |>
   ; accesses := ea
   ; accounts := empty_accounts |>
in
  (ISR x, (HD y.contexts).stack)
``

*)

val _ = export_theory();
