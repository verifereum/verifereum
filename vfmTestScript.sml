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
  set_goal([], thm_term);
  Globals.max_print_depth := 32
*)
fun mk_tactic num_steps =
  rw[run_block_SOME_with_fuel]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ exists_tac (numSyntax.term_of_int num_steps)
  \\ cv_eval_run_block_with_fuel_tac
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
    else
      r_tm |> optionSyntax.dest_some |>
        pairSyntax.dest_pair |> snd |>
        pairSyntax.dest_pair |> snd |>
        numSyntax.int_of_term |>
        curry op - n
  end
  val num_steps = loop n
  val () = TextIO.print $ msg "Found" num_steps
in
  num_steps
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
        "update_account (",
        s,
        ")(n2w ", #address a, ") <|",
        " nonce := ", #nonce a,
        ";balance := ", #balance a,
        ";code := ", case Redblackmap.peek(!codeCache, #code a) of
                          NONE => mk_code_syntax $ #code a
                        | SOME name => name,
        ";storage := ",
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

(*
  val test_index = 0
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
        ";to := n2w ", #to transaction,
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
    val pre_def = new_definition(pre_name,
      Term[QUOTE(pre_name ^ " = " ^ accounts_term pre)]);

    val post = #post test;
    val post_name = test_name_escaped ^ "_post";
    val post_prefix = post_name ^ "_";
    val code_defs = mk_code_defs post_prefix code_defs post;
    val post_def = new_definition(post_name,
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

    (* TODO: save the result to give to mk_tactic *)
    val num_steps = find_num_steps thm_term
  in
    store_thm(thm_name, thm_term, mk_tactic num_steps)
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
val thms = List.tabulate (1, prove_test);
(* TODO: need check for existing account?
val thms = List.tabulate (num_tests, prove_test);
*)

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

(* TODO: fails to parse transaction def?
val test_path = mk_test_path "CrashingTransaction.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stBadOpcode/" ^ s;

val test_path = mk_test_path "eip2315NotRemoved.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix at least d31g0v0
val test_path = mk_test_path "invalidAddr.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: fix at least d24g0v0
val test_path = mk_test_path "invalidDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: fix
val test_path = mk_test_path "measureGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: fix
val test_path = mk_test_path "opc0CDiffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: add
opc0DDiffPlaces.json
opc0EDiffPlaces.json
opc0FDiffPlaces.json
opc1EDiffPlaces.json
opc1FDiffPlaces.json
opc21DiffPlaces.json
opc22DiffPlaces.json
opc23DiffPlaces.json
opc24DiffPlaces.json
opc25DiffPlaces.json
opc26DiffPlaces.json
opc27DiffPlaces.json
opc28DiffPlaces.json
opc29DiffPlaces.json
opc2ADiffPlaces.json
opc2BDiffPlaces.json
opc2CDiffPlaces.json
opc2DDiffPlaces.json
opc2EDiffPlaces.json
opc2FDiffPlaces.json
opc49DiffPlaces.json
opc4ADiffPlaces.json
opc4BDiffPlaces.json
opc4CDiffPlaces.json
opc4DDiffPlaces.json
opc4EDiffPlaces.json
opc4FDiffPlaces.json
opc5CDiffPlaces.json
opc5DDiffPlaces.json
opc5EDiffPlaces.json
opc5FDiffPlaces.json
opcA5DiffPlaces.json
opcA6DiffPlaces.json
opcA7DiffPlaces.json
opcA8DiffPlaces.json
opcA9DiffPlaces.json
opcAADiffPlaces.json
opcABDiffPlaces.json
opcACDiffPlaces.json
opcADDiffPlaces.json
opcAEDiffPlaces.json
opcAFDiffPlaces.json
opcB0DiffPlaces.json
opcB1DiffPlaces.json
opcB2DiffPlaces.json
opcB3DiffPlaces.json
opcB4DiffPlaces.json
opcB5DiffPlaces.json
opcB6DiffPlaces.json
opcB7DiffPlaces.json
opcB8DiffPlaces.json
opcB9DiffPlaces.json
opcBADiffPlaces.json
opcBBDiffPlaces.json
opcBCDiffPlaces.json
opcBDDiffPlaces.json
opcBEDiffPlaces.json
opcBFDiffPlaces.json
opcC0DiffPlaces.json
opcC1DiffPlaces.json
opcC2DiffPlaces.json
opcC3DiffPlaces.json
opcC4DiffPlaces.json
opcC5DiffPlaces.json
opcC6DiffPlaces.json
opcC7DiffPlaces.json
opcC8DiffPlaces.json
opcC9DiffPlaces.json
opcCADiffPlaces.json
opcCBDiffPlaces.json
opcCCDiffPlaces.json
opcCDDiffPlaces.json
opcCEDiffPlaces.json
opcCFDiffPlaces.json
opcD0DiffPlaces.json
opcD1DiffPlaces.json
opcD2DiffPlaces.json
opcD3DiffPlaces.json
opcD4DiffPlaces.json
opcD5DiffPlaces.json
opcD6DiffPlaces.json
opcD7DiffPlaces.json
opcD8DiffPlaces.json
opcD9DiffPlaces.json
opcDADiffPlaces.json
opcDBDiffPlaces.json
opcDCDiffPlaces.json
opcDDDiffPlaces.json
opcDEDiffPlaces.json
opcDFDiffPlaces.json
opcE0DiffPlaces.json
opcE1DiffPlaces.json
opcE2DiffPlaces.json
opcE3DiffPlaces.json
opcE4DiffPlaces.json
opcE5DiffPlaces.json
opcE6DiffPlaces.json
opcE7DiffPlaces.json
opcE8DiffPlaces.json
opcE9DiffPlaces.json
opcEADiffPlaces.json
opcEBDiffPlaces.json
opcECDiffPlaces.json
opcEDDiffPlaces.json
opcEEDiffPlaces.json
opcEFDiffPlaces.json
opcF6DiffPlaces.json
opcF7DiffPlaces.json
opcF8DiffPlaces.json
opcF9DiffPlaces.json
opcFBDiffPlaces.json
opcFCDiffPlaces.json
opcFEDiffPlaces.json
operationDiffGas.json
undefinedOpcodeFirstByte.json
*)

fun mk_test_path s = "tests/BlockchainTests/GeneralStateTests/stBugs/" ^ s;

(* TODO: fix
val test_path = mk_test_path "randomStatetestDEFAULT-Tue_07_58_41-15153-575192.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: fix
val test_path = mk_test_path
"randomStatetestDEFAULT-Tue_07_58_41-15153-575192_london.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

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

(* TODO: fix
val test_path = mk_test_path "callcallcall_000_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "callcallcall_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix
val test_path = mk_test_path "callcallcallcode_001.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

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

(* TODO: fix
val test_path = mk_test_path "callcallcallcode_001_SuicideMiddle.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "callcallcallcode_ABCB_RECURSIVE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix
val test_path = mk_test_path "callcallcode_01.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "callcallcode_01_OOGE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcallcode_01_SuicideEnd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix
val test_path = mk_test_path "callcallcodecall_010.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(*
callcallcodecall_010_OOGE.json
callcallcodecall_010_OOGMAfter.json
callcallcodecall_010_OOGMBefore.json
callcallcodecall_010_SuicideEnd.json
callcallcodecall_010_SuicideMiddle.json
callcallcodecall_ABCB_RECURSIVE.json
callcallcodecallcode_011.json
callcallcodecallcode_011_OOGE.json
callcallcodecallcode_011_OOGMAfter.json
callcallcodecallcode_011_OOGMBefore.json
callcallcodecallcode_011_SuicideEnd.json
callcallcodecallcode_011_SuicideMiddle.json
callcallcodecallcode_ABCB_RECURSIVE.json
callcodeDynamicCode.json
callcodeDynamicCode2SelfCall.json
callcodeEmptycontract.json
callcodeInInitcodeToEmptyContract.json
callcodeInInitcodeToExisContractWithVTransferNEMoney.json
callcodeInInitcodeToExistingContract.json
callcodeInInitcodeToExistingContractWithValueTransfer.json
callcode_checkPC.json
callcodecall_10.json
callcodecall_10_OOGE.json
callcodecall_10_SuicideEnd.json
callcodecallcall_100.json
callcodecallcall_100_OOGE.json
callcodecallcall_100_OOGMAfter.json
callcodecallcall_100_OOGMBefore.json
callcodecallcall_100_SuicideEnd.json
callcodecallcall_100_SuicideMiddle.json
callcodecallcall_ABCB_RECURSIVE.json
callcodecallcallcode_101.json
callcodecallcallcode_101_OOGE.json
callcodecallcallcode_101_OOGMAfter.json
callcodecallcallcode_101_OOGMBefore.json
callcodecallcallcode_101_SuicideEnd.json
callcodecallcallcode_101_SuicideMiddle.json
callcodecallcallcode_ABCB_RECURSIVE.json
callcodecallcode_11.json
callcodecallcode_11_OOGE.json
callcodecallcode_11_SuicideEnd.json
callcodecallcodecall_110.json
callcodecallcodecall_110_OOGE.json
callcodecallcodecall_110_OOGMAfter.json
callcodecallcodecall_110_OOGMBefore.json
callcodecallcodecall_110_SuicideEnd.json
callcodecallcodecall_110_SuicideMiddle.json
callcodecallcodecall_ABCB_RECURSIVE.json
callcodecallcodecallcode_111.json
callcodecallcodecallcode_111_OOGE.json
callcodecallcodecallcode_111_OOGMAfter.json
callcodecallcodecallcode_111_OOGMBefore.json
callcodecallcodecallcode_111_SuicideEnd.json
callcodecallcodecallcode_111_SuicideMiddle.json
callcodecallcodecallcode_ABCB_RECURSIVE.json
*)

(*

cv_eval ``
let acc = blockInfo_d0g0v0_Cancun_pre in
let blk = blockInfo_d0g0v0_Cancun_block in
let tx = blockInfo_d0g0v0_Cancun_transaction in
let s = (THE $ initial_state 1 [] blk acc
               empty_return_destination tx) with accounts updated_by
           transfer_value tx.from tx.to tx.value in
let (r, s) = run_n 6 s in
let c = EL 0 s.contexts in
  (LENGTH s.contexts, c.stack, c.returnData, c.gasUsed,
   c.callParams.gasLimit,
   c.pc,
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
   (lookup_storage (lookup_account s.accounts c.callParams.callee).storage 0w)
   )
``

*)

val _ = export_theory();
