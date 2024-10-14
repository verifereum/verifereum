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

val _ = new_theory "debug";

fun mk_statement test_name =
  Term[QUOTE(String.concat[
         "∃rs. run_block 1 ",
         test_name, "_pre ",
         test_name, "_block ",
         "= SOME (rs, ",
         test_name, "_post)"])]

val run_block_with_fuel =
  run_block_with_fuel_def |> SPEC_ALL |> concl |> lhs
  |> strip_comb |> fst;

fun trim2 s = Substring.string(Substring.triml 2 (Substring.full s))

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

val test_path = "tests/mload.json";
val test_index = 1;

val test_names = get_test_names test_path;
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

val thm_term = mk_statement test_name;

val (_, args) = dest_exists thm_term |> snd |> lhs |> strip_comb
val n = 14
val n_tm = numSyntax.term_of_int n
val run_tm = list_mk_comb(run_block_with_fuel, n_tm::args)

(* now pray... *)
val raw_th = cv_eval_raw run_tm

val _ = export_theory();
