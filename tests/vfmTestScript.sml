open HolKernel boolLib bossLib Parse wordsLib dep_rewrite permLib
     listTheory pairTheory optionTheory sumTheory
     arithmeticTheory combinTheory whileTheory
     sortingTheory wordsTheory
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

fun mk_statement isHash test_name =
  if isHash then
    Term[QUOTE(String.concat[
           "∃n1 n2 m. run_block_to_hash n1 n2 1 [] ", (* TODO: add prev hashes if needed *)
           test_name, "_pre ",
           test_name, "_block ",
           "= SOME (m, SOME ",
           test_name, "_post)"])]
  else
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

val run_block_to_hash = run_block_to_hash_def |> SPEC_ALL
  |> concl |> lhs |> strip_comb |> fst;
val trie_steps = 65536
val trie_n = numSyntax.term_of_int trie_steps

Definition switch_def:
  switch x d [] = d ∧
  switch x d ((y,z)::ls) =
  if x = y then z else switch x d ls
End

Theorem COND_right_switch1:
  COND (x = b) y z = switch b z [(x,y)]
Proof
  rw[switch_def]
QED

Theorem switch1_switch:
  switch x (switch x d ls) [p] =
  switch x d (p::ls)
Proof
  Cases_on`p` \\ rw[switch_def]
QED

Theorem PERM_switch:
  !l1 l2. PERM l1 l2 ⇒ ALL_DISTINCT (MAP FST l1) ⇒
  switch b d l1 = switch b d l2
Proof
  ho_match_mp_tac PERM_STRONG_IND
  \\ rw[] \\ gs[]
  >- ( Cases_on`x` \\ rw[switch_def] )
  >- (
    Cases_on`x` \\ Cases_on`y`
    \\ rw[switch_def] \\ gs[] )
  \\ first_x_assum irule
  \\ metis_tac[PERM_MAP, ALL_DISTINCT_PERM]
QED

Theorem irreflexive_transitive_word_lo:
  irreflexive (word_lo:bytes32 -> bytes32 -> bool) ∧
  transitive  (word_lo:bytes32 -> bytes32 -> bool)
Proof
  rw[relationTheory.irreflexive_def, relationTheory.transitive_def]
  \\ irule WORD_LOWER_TRANS
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ first_x_assum ACCEPT_TAC
QED

fun word_w2n_lt t1 t2 = let
  val n1 = t1 |> rand |> numSyntax.dest_numeral
  val n2 = t2 |> rand |> numSyntax.dest_numeral
in Arbnum.< (n1, n2) end

(*
  set_goal([], thm_term)
*)
fun mk_tactic num_steps eval_th =
  rw[run_block_SOME_with_fuel, PULL_EXISTS]
  \\ CONV_TAC (RESORT_EXISTS_CONV(sort_vars["n"]))
  \\ exists_tac num_steps
  \\ rewrite_tac[eval_th]
  \\ rewrite_tac cv_eval_run_block_with_fuel_rwts
  \\ rewrite_tac[LET_THM]
  \\ CONV_TAC(ONCE_DEPTH_CONV (BETA_CONV THENC EVAL))
  \\ rewrite_tac[SOME_11, PAIR_EQ]
  \\ Ho_Rewrite.REWRITE_TAC[UNWIND_THM1]
  \\ rewrite_tac[FUN_EQ_THM] \\ gen_tac
  \\ rewrite_tac[APPLY_UPDATE_THM]
  \\ CONV_TAC(RAND_CONV EVAL)
  \\ rpt (
     IF_CASES_TAC >- (
       BasicProvers.VAR_EQ_TAC
       \\ CONV_TAC(ONCE_DEPTH_CONV word_EQ_CONV)
       \\ rewrite_tac account_rwts
       \\ rpt gen_tac
       \\ rewrite_tac[COND_right_switch1, switch1_switch]
       \\ irule PERM_switch
       \\ (conj_tac >- (
         rewrite_tac[MAP, FST]
         \\ CONV_TAC (
              ALL_DISTINCT_CONV
                irreflexive_transitive_word_lo
                word_w2n_lt
                (EQT_INTRO o wordsLib.WORD_DECIDE)
            )))
       \\ CONV_TAC(PERM_NORMALISE_CONV)
       \\ rewrite_tac[])
     \\ rewrite_tac [])
  \\ rewrite_tac account_rwts

fun mk_tactic_hash eval_th = let
  val args = eval_th |> concl |> lhs |> strip_comb |> #2
in
  exists_tac (el 1 args)
  \\ exists_tac (el 2 args)
  \\ rewrite_tac[eval_th]
  \\ rewrite_tac[to_option_def, SOME_11, to_pair_def, PAIR_EQ]
  \\ Ho_Rewrite.REWRITE_TAC[UNWIND_THM1]
  \\ EVAL_TAC
end

fun find_num_steps isHash thm_term =
let
  val (_, args) = strip_exists thm_term |> snd |> lhs |> strip_comb
  val name = last args |> dest_const |> fst
  fun msg pre n = pre ^ " num steps " ^ Int.toString n ^ " for " ^ name ^ "\n"
  val n = 65536
  fun loop n =
  let
    val () = TextIO.print $ msg "Trying" n
    val n_tm = numSyntax.term_of_int n
    val run_tm = if isHash
      then list_mk_comb(run_block_to_hash, n_tm::trie_n::(List.drop(args, 2)))
      else list_mk_comb(run_block_with_fuel, n_tm::args)
    val raw_th = cv_eval_raw run_tm
    val r_tm = raw_th |>
      REWRITE_RULE[to_option_def, to_pair_def, c2n_def] |>
      concl |> rhs
  in
    if optionSyntax.is_none r_tm
    then loop $ 512 * n
    else (raw_th, n)
  end
  val (raw_th, n) = loop n
in
  if isHash then
    (numSyntax.zero_tm, raw_th)
  else let
    val zero_th = MATCH_MP run_block_with_fuel_cv_sub raw_th
                  |> CONV_RULE (PATH_CONV "lrllllr" numLib.REDUCE_CONV)
    val num_steps = zero_th |> concl |> lhs |> strip_comb |>
                    #2 |> el 1
    val () = TextIO.print $ msg "Found" $ numSyntax.int_of_term num_steps
  in
    (num_steps, zero_th)
  end
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

fun entry_term {address, storageKeys} = let
  val keys = List.map (fn s => "n2w " ^ s ) storageKeys |> String.concatWith "; "
in
  String.concat["<| account := n2w ", address,
                 "; keys := [", keys, "] |>"]
end

fun accesses_term ls =
  String.concat["[", String.concatWith "; " (List.map entry_term ls), "]"]

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

fun remove_special_chars #"-" = "_"
  | remove_special_chars #"^" = "N"
  | remove_special_chars #"+" = "P"
  | remove_special_chars c = String.str c

(*
  val test_index = 0;
  val () = Globals.max_print_depth := 30;
  val json_path = test_path


  fun findIndexByName (name:string) (l: string list) = let
  fun aux [] _ = NONE
     | aux (x::xs) (n:int) =
       if name = x
       then SOME n
       else aux xs (n+1)
  in
    aux l 0
  end

  val SOME test_index = findIndexByName "sha3_d3g0v0_Cancun" test_names
*)

fun mk_prove_test test_path = let
  val test_names = get_test_names test_path;
  fun prove_test test_index = let
    val test_name = List.nth(test_names, test_index);
    val test_name_escaped =
      let
        val e = String.translate remove_special_chars test_name
      in
        if Char.isDigit $ String.sub (e, 0) then "t" ^ e else e
      end
    val test = get_test test_path test_name;
    val isHash = not $ Option.isSome $ #post test;

    val block = #block test;

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
        ";gasPrice := ", case #gasPrice transaction of SOME n => n
                         | _ => String.concat [
                                  "effective_gas_price ",
                                  #baseFeePerGas block, " ",
                                  Option.valOf $ #maxFeePerGas transaction, " ",
                                  Option.valOf $
                                    #maxPriorityFeePerGas transaction
                                ],
        ";gasLimit := ", #gasLimit transaction,
        ";accessList := ", accesses_term $ #accessList transaction, " |>"
      ])]);

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

    val post_name = test_name_escaped ^ "_post";
    val post_prefix = post_name ^ "_";
    val (post_def, code_defs) =
      case #post test of SOME post => let
        val code_defs = mk_code_defs post_prefix code_defs post;
        val post_def = new_definition(post_name ^ "_def",
          Term[QUOTE(post_name ^ " = " ^ accounts_term post)]);
      in (post_def, code_defs) end
      | _ => let
        val post = Option.valOf $ #postHash test;
        val bytes = String.concat["REVERSE $ hex_to_rev_bytes [] \"",
                                  trim2 post, "\""]
        val post_def = new_definition(post_name ^ "_def",
          Term[QUOTE(post_name ^ " = " ^ bytes)])
      in (post_def, code_defs) end

    val () = List.app (cv_trans_deep_embedding EVAL) code_defs;
    val () = cv_auto_trans pre_def;
    val () = cv_auto_trans post_def;
    val () = cv_auto_trans transaction_def;
    val () = cv_auto_trans block_def;
    val () = computeLib.add_funs [pre_def, post_def, transaction_def, block_def]
    val () = computeLib.add_funs code_defs;

    val thm_name = test_name_escaped ^ "_correctness";
    val thm_term = mk_statement isHash test_name_escaped;

    val (num_steps, eval_th) = find_num_steps isHash thm_term
  in
    store_thm(thm_name, thm_term,
              (if isHash then mk_tactic_hash else mk_tactic num_steps) eval_th)
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

val test_path = mk_test_path "vmIOandFlowOperations/jumpToPush.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

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

val test_path = mk_test_path "vmLogTest/log0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmLogTest/log1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmLogTest/log2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmLogTest/log3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "vmLogTest/log4.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

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

(* TODO: add
fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/Pyspecs/" ^ s;

needs support for old block types
val test_path = mk_test_path "berlin/eip2930_access_list/access_list.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/Cancun/" ^ s;

val test_path = mk_test_path
  "stEIP1153-transientStorage/10_revertUndoesStoreAfterReturn.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "stEIP1153-transientStorage/14_revertAfterNestedStaticcall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow - cache num steps
val test_path = mk_test_path
  "stEIP1153-transientStorage/15_tstoreCannotBeDosd.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path
  "stEIP1153-transientStorage/17_tstoreGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "stEIP1153-transientStorage/19_oogUndoesTransientStore.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow - cache num steps
val test_path = mk_test_path
  "stEIP1153-transientStorage/21_tstoreCannotBeDosdOOO.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "stEIP1153-transientStorage/transStorageOK.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stEIP1153-transientStorage/transStorageReset.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: add stEIP4844-blobtransactions *)

val test_path = mk_test_path "stEIP5656-MCOPY/MCOPY.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stEIP5656-MCOPY/MCOPY_copy_cost.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stEIP5656-MCOPY/MCOPY_memory_expansion_cost.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stEIP5656-MCOPY/MCOPY_memory_hash.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/Shanghai/" ^ s;

val test_path = mk_test_path "stEIP3651-warmcoinbase/coinbaseWarmAccountCallGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "stEIP3651-warmcoinbase/coinbaseWarmAccountCallGasFail.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stEIP3855-push0/push0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stEIP3855-push0/push0Gas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stEIP3855-push0/push0Gas2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow
val test_path = mk_test_path
  "stEIP3860-limitmeterinitcode/create2InitCodeSizeLimit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path
  "stEIP3860-limitmeterinitcode/createInitCodeSizeLimit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow / oom
val test_path = mk_test_path
  "stEIP3860-limitmeterinitcode/creationTxInitCodeSizeLimit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

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

val test_path = mk_test_path "log0NonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log1NonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log2NonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3NonConst.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

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

(* TODO: fix from d41g0v0 (needs more precompiles?)
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

(* TODO: slow
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

(* TODO: slow
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

(* TODO: slow
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

val test_path = mk_test_path "RevertInCreateInInitCreate2Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

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

(* TODO: parse error from d0g28v0 *)
val test_path = mk_test_path "intrinsic.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

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

val test_path = mk_test_path "senderBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

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

val test_path = mk_test_path "typeTwoBerlin.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: parse error from d0g0v1 - need expectException
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

val test_path = mk_test_path "addressOpcodes.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "coinbaseT01.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "coinbaseT2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "manualCreate.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "storageCosts.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "transactionCosts.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "variedContext.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

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

val test_path = mk_test_path "accessListExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "add11.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "add11_yml.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "basefeeExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "eip1559.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

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

val test_path = mk_test_path "mergeTest.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "rangesExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "solidityExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "yulExample.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stExtCodeHash/" ^ s;

val test_path = mk_test_path "callToNonExistent.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callToSuicideThenExtcodehash.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "codeCopyZero_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createEmptyThenExtcodehash.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "dynamicAccountOverwriteEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeCopyBounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashAccountWithoutCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashCALL.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashCALLCODE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashChangedAccount.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashCreatedAndDeletedAccount.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashCreatedAndDeletedAccountCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "extCodeHashCreatedAndDeletedAccountRecheckInOuterCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashCreatedAndDeletedAccountStaticCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashDELEGATECALL.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashDeletedAccount.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashDeletedAccount1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashDeletedAccount1Cancun.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashDeletedAccount2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashDeletedAccount2Cancun.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashDeletedAccount3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashDeletedAccount4.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashDeletedAccountCancun.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashDynamicArgument.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashInInitCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashMaxCodeSize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashNewAccount.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashNonExistingAccount.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashPrecompiles.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashSTATICCALL.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashSelf.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashSelfInInit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashSubcallOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashSubcallSuicide.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extCodeHashSubcallSuicideCancun.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extcodehashEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stHomesteadSpecific/" ^ s;

val test_path = mk_test_path "contractCreationOOGdontLeaveEmptyContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "contractCreationOOGdontLeaveEmptyContractViaTransaction.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createContractViaContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createContractViaContractOOGInitCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createContractViaTransactionCost53000.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stInitCodeTest/" ^ s;

val test_path = mk_test_path "CallContractToCreateContractAndCallItOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallContractToCreateContractNoCash.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallContractToCreateContractOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallContractToCreateContractOOGBonusGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "CallContractToCreateContractWhichWouldCreateContractIfCalled.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallRecursiveContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallTheContractToCreateEmptyContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "OutOfGasContractCreation.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "OutOfGasPrefundedContractCreation.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ReturnTest.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ReturnTest2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "StackUnderFlowContractCreation.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TransactionCreateAutoSuicideContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TransactionCreateRandomInitCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TransactionCreateStopInInitcode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TransactionCreateSuicideInInitcode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stLogTests/" ^ s;

val test_path = mk_test_path "log0_emptyMem.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log0_logMemStartTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log0_logMemsizeTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log0_logMemsizeZero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log0_nonEmptyMem.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log0_nonEmptyMem_logMemSize1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log0_nonEmptyMem_logMemSize1_logMemStart31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log1_Caller.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log1_MaxTopic.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log1_emptyMem.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log1_logMemStartTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log1_logMemsizeTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log1_logMemsizeZero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log1_nonEmptyMem.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log1_nonEmptyMem_logMemSize1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log1_nonEmptyMem_logMemSize1_logMemStart31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log2_Caller.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log2_MaxTopic.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log2_emptyMem.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log2_logMemStartTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log2_logMemsizeTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log2_logMemsizeZero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log2_nonEmptyMem.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log2_nonEmptyMem_logMemSize1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log2_nonEmptyMem_logMemSize1_logMemStart31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3_Caller.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3_MaxTopic.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3_PC.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3_emptyMem.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3_logMemStartTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3_logMemsizeTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3_logMemsizeZero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3_nonEmptyMem.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3_nonEmptyMem_logMemSize1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3_nonEmptyMem_logMemSize1_logMemStart31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log4_Caller.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log4_MaxTopic.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log4_PC.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log4_emptyMem.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log4_logMemStartTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log4_logMemsizeTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log4_logMemsizeZero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log4_nonEmptyMem.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log4_nonEmptyMem_logMemSize1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log4_nonEmptyMem_logMemSize1_logMemStart31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "logInOOG_Call.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stMemExpandingEIP150Calls/" ^ s;

val test_path = mk_test_path
  "CallAndCallcodeConsumeMoreGasThenTransactionHasWithMemExpandingCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "CallAskMoreGasOnDepth2ThenTransactionHasWithMemExpandingCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallGoesOOGOnSecondLevel2WithMemExpandingCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallGoesOOGOnSecondLevelWithMemExpandingCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateAndGasInsideCreateWithMemExpandingCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "DelegateCallOnEIPWithMemExpandingCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "ExecuteCallThatAskMoreGasThenTransactionHasWithMemExpandingCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NewGasPriceForCodesWithMemExpandingCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "OOGinReturn.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stMemoryStressTest/" ^ s;

val test_path = mk_test_path "CALLCODE_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CALLCODE_Bounds2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CALLCODE_Bounds3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CALLCODE_Bounds4.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CALL_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CALL_Bounds2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CALL_Bounds2a.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CALL_Bounds3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_Bounds2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CREATE_Bounds3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "DELEGATECALL_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "DELEGATECALL_Bounds2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "DELEGATECALL_Bounds3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "DUP_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "FillStack.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "JUMPI_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "JUMP_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "JUMP_Bounds2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "MLOAD_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "MLOAD_Bounds2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "MLOAD_Bounds3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "MSTORE_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "MSTORE_Bounds2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "MSTORE_Bounds2a.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "POP_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RETURN_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "SLOAD_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "SSTORE_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mload32bitBound.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mload32bitBound2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mload32bitBound_Msize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mload32bitBound_return.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mload32bitBound_return2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_CALL_Bounds.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_CALL_Bounds2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_CALL_Bounds2a.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_CALL_Bounds3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stMemoryTest/" ^ s;

val test_path = mk_test_path "buffer.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "bufferSrcOffset.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callDataCopyOffset.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "calldatacopy_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "calldatacopy_dejavu2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "codeCopyOffset.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "codecopy_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "codecopy_dejavu2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extcodecopy_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log1_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log2_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log3_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "log4_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem0b_singleByte.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem31b_singleByte.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32b_singleByte.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb+1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb+31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb+32.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb+33.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb-1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb-31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb-32.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb-33.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb_singleByte+1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb_singleByte+31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb_singleByte+32.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb_singleByte+33.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb_singleByte-1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb_singleByte-31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb_singleByte-32.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb_singleByte-33.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem32kb_singleByte.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem33b_singleByte.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb+1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb+31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb+32.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb+33.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb-1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb-31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb-32.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb-33.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb_singleByte+1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb_singleByte+31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb_singleByte+32.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb_singleByte+33.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb_singleByte-1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb_singleByte-31.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb_singleByte-32.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb_singleByte-33.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mem64kb_singleByte.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "memCopySelf.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "memReturn.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mload16bitBound.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mload8bitBound.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mload_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mstore_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "mstroe8_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow
val test_path = mk_test_path "oog.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "sha3_dejavu.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackLimitGas_1023.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackLimitGas_1024.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackLimitGas_1025.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackLimitPush31_1023.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackLimitPush31_1024.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackLimitPush31_1025.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackLimitPush32_1023.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackLimitPush32_1024.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackLimitPush32_1025.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stNonZeroCallsTest/" ^ s;

val test_path = mk_test_path "NonZeroValue_CALL.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_CALLCODE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_CALLCODE_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_CALLCODE_ToNonNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_CALLCODE_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_CALL_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_CALL_ToNonNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_CALL_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_DELEGATECALL.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_DELEGATECALL_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_DELEGATECALL_ToNonNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_DELEGATECALL_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_SUICIDE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_SUICIDE_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_SUICIDE_ToNonNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_SUICIDE_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_TransactionCALL.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_TransactionCALL_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_TransactionCALL_ToNonNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_TransactionCALL_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_TransactionCALLwithData.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NonZeroValue_TransactionCALLwithData_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "NonZeroValue_TransactionCALLwithData_ToNonNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "NonZeroValue_TransactionCALLwithData_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stPreCompiledContracts/" ^ s;

(* TODO: add blake2B.json *)

val test_path = mk_test_path "delegatecall09Undefined.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix
val test_path = mk_test_path "idPrecomps.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "identity_to_smaller.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "identity_to_bigger.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "modexp.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "modexpTests.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: add
precompsEIP2929Cancun.json
*)

(* TODO: fix
val test_path = mk_test_path "sec80.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: add stPreCompiledContracts2 *)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stQuadraticComplexityTest/" ^ s;

val test_path = mk_test_path "Call1MB1024Calldepth.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow
val test_path = mk_test_path "Call20KbytesContract50_1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: slow
val test_path = mk_test_path "Call20KbytesContract50_2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: probably slow
val test_path = mk_test_path "Call20KbytesContract50_3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Call50000.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Call50000_ecrec.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Call50000_identity.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Call50000_identity2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Call50000_rip160.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Call50000_sha256.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Callcode50000.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create1000.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create1000Byzantium.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Create1000Shnghai.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "QuadraticComplexitySolidity_CallDataCopy.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Return50000.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Return50000_2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stRandom/" ^ s;

val test_path = mk_test_path "randomStatetest0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest10.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest100.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest102.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest103.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest104.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest105.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest106.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest107.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix slow rewrite_tac cv_eval_run_block_with_fuel_rwts *)
val test_path = mk_test_path "randomStatetest108.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest11.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest110.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest111.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest112.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest114.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest115.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest116.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest117.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest118.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest119.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest12.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest120.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest121.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest122.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest124.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest125.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest126.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest129.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest13.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest130.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest131.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest133.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest134.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest135.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest137.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest138.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "randomStatetest139.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: add
randomStatetest14.json
randomStatetest142.json
randomStatetest143.json
randomStatetest144.json
randomStatetest145.json
randomStatetest146.json
randomStatetest147.json
randomStatetest148.json
randomStatetest149.json
randomStatetest15.json
randomStatetest150.json
randomStatetest151.json
randomStatetest153.json
randomStatetest154.json
randomStatetest155.json
randomStatetest156.json
randomStatetest157.json
randomStatetest158.json
randomStatetest159.json
randomStatetest16.json
randomStatetest161.json
randomStatetest162.json
randomStatetest163.json
randomStatetest164.json
randomStatetest166.json
randomStatetest167.json
randomStatetest169.json
randomStatetest17.json
randomStatetest171.json
randomStatetest172.json
randomStatetest173.json
randomStatetest174.json
randomStatetest175.json
randomStatetest176.json
randomStatetest177.json
randomStatetest178.json
randomStatetest179.json
randomStatetest18.json
randomStatetest180.json
randomStatetest183.json
randomStatetest184.json
randomStatetest185.json
randomStatetest187.json
randomStatetest188.json
randomStatetest189.json
randomStatetest19.json
randomStatetest190.json
randomStatetest191.json
randomStatetest192.json
randomStatetest194.json
randomStatetest195.json
randomStatetest196.json
randomStatetest197.json
randomStatetest198.json
randomStatetest199.json
randomStatetest2.json
randomStatetest20.json
randomStatetest200.json
randomStatetest201.json
randomStatetest202.json
randomStatetest204.json
randomStatetest205.json
randomStatetest206.json
randomStatetest207.json
randomStatetest208.json
randomStatetest209.json
randomStatetest210.json
randomStatetest211.json
randomStatetest212.json
randomStatetest214.json
randomStatetest215.json
randomStatetest216.json
randomStatetest217.json
randomStatetest219.json
randomStatetest22.json
randomStatetest220.json
randomStatetest221.json
randomStatetest222.json
randomStatetest225.json
randomStatetest226.json
randomStatetest227.json
randomStatetest228.json
randomStatetest23.json
randomStatetest230.json
randomStatetest231.json
randomStatetest232.json
randomStatetest233.json
randomStatetest236.json
randomStatetest237.json
randomStatetest238.json
randomStatetest24.json
randomStatetest242.json
randomStatetest243.json
randomStatetest244.json
randomStatetest245.json
randomStatetest246.json
randomStatetest247.json
randomStatetest248.json
randomStatetest249.json
randomStatetest25.json
randomStatetest250.json
randomStatetest251.json
randomStatetest252.json
randomStatetest254.json
randomStatetest257.json
randomStatetest259.json
randomStatetest26.json
randomStatetest260.json
randomStatetest261.json
randomStatetest263.json
randomStatetest264.json
randomStatetest265.json
randomStatetest266.json
randomStatetest267.json
randomStatetest268.json
randomStatetest269.json
randomStatetest27.json
randomStatetest270.json
randomStatetest271.json
randomStatetest273.json
randomStatetest274.json
randomStatetest275.json
randomStatetest276.json
randomStatetest278.json
randomStatetest279.json
randomStatetest28.json
randomStatetest280.json
randomStatetest281.json
randomStatetest282.json
randomStatetest283.json
randomStatetest285.json
randomStatetest286.json
randomStatetest287.json
randomStatetest288.json
randomStatetest29.json
randomStatetest290.json
randomStatetest291.json
randomStatetest292.json
randomStatetest293.json
randomStatetest294.json
randomStatetest295.json
randomStatetest296.json
randomStatetest297.json
randomStatetest298.json
randomStatetest299.json
randomStatetest3.json
randomStatetest30.json
randomStatetest300.json
randomStatetest301.json
randomStatetest302.json
randomStatetest303.json
randomStatetest304.json
randomStatetest305.json
randomStatetest306.json
randomStatetest307.json
randomStatetest308.json
randomStatetest309.json
randomStatetest31.json
randomStatetest310.json
randomStatetest311.json
randomStatetest312.json
randomStatetest313.json
randomStatetest315.json
randomStatetest316.json
randomStatetest318.json
randomStatetest320.json
randomStatetest321.json
randomStatetest322.json
randomStatetest323.json
randomStatetest325.json
randomStatetest326.json
randomStatetest327.json
randomStatetest329.json
randomStatetest33.json
randomStatetest332.json
randomStatetest333.json
randomStatetest334.json
randomStatetest335.json
randomStatetest336.json
randomStatetest337.json
randomStatetest338.json
randomStatetest339.json
randomStatetest340.json
randomStatetest341.json
randomStatetest342.json
randomStatetest343.json
randomStatetest345.json
randomStatetest346.json
randomStatetest347.json
randomStatetest348.json
randomStatetest349.json
randomStatetest350.json
randomStatetest351.json
randomStatetest352.json
randomStatetest353.json
randomStatetest354.json
randomStatetest355.json
randomStatetest356.json
randomStatetest357.json
randomStatetest358.json
randomStatetest359.json
randomStatetest36.json
randomStatetest360.json
randomStatetest361.json
randomStatetest362.json
randomStatetest363.json
randomStatetest364.json
randomStatetest365.json
randomStatetest366.json
randomStatetest367.json
randomStatetest368.json
randomStatetest369.json
randomStatetest37.json
randomStatetest370.json
randomStatetest371.json
randomStatetest372.json
randomStatetest376.json
randomStatetest378.json
randomStatetest379.json
randomStatetest380.json
randomStatetest381.json
randomStatetest382.json
randomStatetest383.json
randomStatetest384.json
randomStatetest39.json
randomStatetest4.json
randomStatetest41.json
randomStatetest42.json
randomStatetest43.json
randomStatetest45.json
randomStatetest47.json
randomStatetest48.json
randomStatetest49.json
randomStatetest5.json
randomStatetest51.json
randomStatetest52.json
randomStatetest53.json
randomStatetest54.json
randomStatetest55.json
randomStatetest57.json
randomStatetest58.json
randomStatetest59.json
randomStatetest6.json
randomStatetest60.json
randomStatetest62.json
randomStatetest63.json
randomStatetest64.json
randomStatetest66.json
randomStatetest67.json
randomStatetest69.json
randomStatetest72.json
randomStatetest73.json
randomStatetest74.json
randomStatetest75.json
randomStatetest77.json
randomStatetest78.json
randomStatetest80.json
randomStatetest81.json
randomStatetest82.json
randomStatetest83.json
randomStatetest84.json
randomStatetest85.json
randomStatetest87.json
randomStatetest88.json
randomStatetest89.json
randomStatetest9.json
randomStatetest90.json
randomStatetest92.json
randomStatetest95.json
randomStatetest96.json
randomStatetest97.json
randomStatetest98.json
*)

(* TODO: add until stRandom2 *)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stRecursiveCreate/" ^ s;

val test_path = mk_test_path "recursiveCreate.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: parse
val test_path = mk_test_path "recursiveCreateReturnValue.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stRefundTest/" ^ s;

val test_path = mk_test_path "refund50_1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund50_2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund50percentCap.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund600.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refundFF.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refundMax.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refundSSTORE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refundSuicide50procentCap.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_CallA.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_CallA_OOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_CallA_notEnoughGasInCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_CallToSuicideNoStorage.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_CallToSuicideStorage.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_CallToSuicideTwice.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_NoOOG_1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_OOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_TxToSuicide.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_TxToSuicideOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_changeNonZeroStorage.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_getEtherBack.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_multimpleSuicide.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "refund_singleSuicide.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stReturnDataTest/" ^ s;

(* TODO: fix - need precompile?
val test_path = mk_test_path "call_ecrec_success_empty_then_returndatasize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path
  "call_outsize_then_create_successful_then_returndatasize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "call_then_call_value_fail_then_returndatasize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "call_then_create_successful_then_returndatasize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "clearReturnBuffer.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "create_callprecompile_returndatasize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix - need precompile?
val test_path = mk_test_path "modexp_modsize0_returndatasize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "returndatacopy_0_0_following_successful_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_afterFailing_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_after_failing_callcode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_after_failing_delegatecall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_after_failing_staticcall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_after_revert_in_staticcall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_after_successful_callcode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_after_successful_delegatecall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_after_successful_staticcall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_following_call.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_following_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_following_failing_call.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_following_revert.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_following_revert_in_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_following_successful_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_following_too_big_transfer.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_initial.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_initial_256.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_initial_big_sum.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatacopy_overrun.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_after_failing_callcode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_after_failing_delegatecall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_after_failing_staticcall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_after_oog_after_deeper.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_after_successful_callcode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_after_successful_delegatecall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_after_successful_staticcall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_bug.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_following_successful_create.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_initial.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "returndatasize_initial_zero_read.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "revertRetDataSize.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "subcallReturnMoreThenExpected.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "tooLongReturnDataCopy.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stRevertTest/" ^ s;

val test_path = mk_test_path "LoopCallsDepthThenRevert.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "LoopCallsDepthThenRevert2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "LoopCallsDepthThenRevert3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "LoopCallsThenRevert.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "LoopDelegateCallsDepthThenRevert.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "NashatyrevSuicideRevert.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "PythonRevertTestTue201814-1430.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertDepth2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertDepthCreateAddressCollision.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertDepthCreateOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertInCallCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertInCreateInInit_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertInDelegateCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertInStaticCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOnEmptyStack.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOpcode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOpcodeCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOpcodeCreate.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOpcodeDirectCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOpcodeInCallsOnNonEmptyReturnData.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOpcodeInCreateReturns.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOpcodeInInit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOpcodeMultipleSubCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOpcodeReturn.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertOpcodeWithBigOutputInInit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix from d0g1v0
val test_path = mk_test_path "RevertPrecompiledTouchExactOOG_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "RevertPrecompiledTouch_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertPrecompiledTouch_nonce.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertPrecompiledTouch_noncestorage.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertPrecompiledTouch_storage_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertPrefound.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertPrefoundCall.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertPrefoundCallOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertPrefoundEmptyCallOOG_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertPrefoundEmptyCall_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertPrefoundEmptyOOG_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertPrefoundEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertPrefoundOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertRemoteSubCallStorageOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertSubCallStorageOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RevertSubCallStorageOOG2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TouchToEmptyAccountRevert2_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TouchToEmptyAccountRevert3_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TouchToEmptyAccountRevert_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "costRevert.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stateRevert.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stSLoadTest/" ^ s;

val test_path = mk_test_path "sloadGasCost.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stSStoreTest/" ^ s;

val test_path = mk_test_path "InitCollisionNonZeroNonce.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "InitCollisionParis.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "SstoreCallToSelfSubRefundBelowZero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstoreGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_0to0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_0to0to0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_0to0toX.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_0toX.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_0toXto0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_0toXto0toX.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_0toXtoX.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_0toXtoY.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_Xto0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_Xto0to0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_Xto0toX.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_Xto0toXto0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_Xto0toY.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_XtoX.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_XtoXto0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_XtoXtoX.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_XtoXtoY.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_XtoY.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_XtoYto0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_XtoYtoX.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_XtoYtoY.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_XtoYtoZ.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_changeFromExternalCallInInitCode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sstore_gasLeft.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stSelfBalance/" ^ s;

val test_path = mk_test_path "diffPlaces.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "selfBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "selfBalanceCallTypes.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "selfBalanceEqualsBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "selfBalanceGasCost.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "selfBalanceUpdate.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stShift/" ^ s;

val test_path = mk_test_path "sar00.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar01.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar10.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar11.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_0_256-1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_2^254_254.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_2^255-1_248.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_2^255-1_254.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_2^255-1_255.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_2^255-1_256.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_2^255_1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_2^255_255.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_2^255_256.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_2^255_257.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow
val test_path = mk_test_path "sar_2^256-1_0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "sar_2^256-1_1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_2^256-1_255.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sar_2^256-1_256.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow
val test_path = mk_test_path "shiftCombinations.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shiftSignedCombinations.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "shl01-0100.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shl01-0101.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shl01-ff.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shl01.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shl10.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shl11.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shl_-1_0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shl_-1_1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shl_-1_255.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shl_-1_256.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shl_2^255-1_1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shr01.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shr10.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shr11.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shr_-1_0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shr_-1_1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shr_-1_255.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shr_-1_256.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shr_2^255_1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shr_2^255_255.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shr_2^255_256.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "shr_2^255_257.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stSolidityTest/" ^ s;

val test_path = mk_test_path "AmbiguousMethod.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ByZero.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallInfiniteLoop.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallLowLevelCreatesSolidity.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallRecursiveMethods.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ContractInheritance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateContractFromMethod.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RecursiveCreateContracts.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "RecursiveCreateContractsCreate4Contracts.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "SelfDestruct.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TestBlockAndTransactionProperties.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TestContractInteraction.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TestContractSuicide.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix
val test_path = mk_test_path "TestCryptographicFunctions.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "TestKeywords.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TestOverflow.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TestStoreGasPrices.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TestStructuresAndVariabless.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stSpecialTest/" ^ s;

val test_path = mk_test_path "FailedCreateRevertsDeletionParis.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow
val test_path = mk_test_path "JUMPDEST_Attack.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "JUMPDEST_AttackwithJump.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "OverflowGasMakeMoney.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "StackDepthLimitSEC.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow
val test_path = mk_test_path "block504980.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "deploymentError.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: parse
val test_path = mk_test_path "eoaEmptyParis.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

val test_path = mk_test_path "failed_tx_xcf416c53_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "gasPrice0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "makeMoney.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "push32withoutByte.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "selfdestructEIP2929.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "sha3_deja.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow
val test_path = mk_test_path "tx_e1c174e2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stStackTests/" ^ s;

val test_path = mk_test_path "shallowStack.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: oom near last test *)
val test_path = mk_test_path "stackOverflow.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: oom near last test *)
val test_path = mk_test_path "stackOverflowDUP.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackOverflowM1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackOverflowM1DUP.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackOverflowM1PUSH.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackOverflowPUSH.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stackOverflowSWAP.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "stacksanitySWAP.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: parse
val test_path = mk_test_path "underflowTest.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stStaticCall/" ^ s;

(* TODO: add
StaticcallToPrecompileFromCalledContract.json
StaticcallToPrecompileFromContractInitialization.json
StaticcallToPrecompileFromTransaction.json
*)

val test_path = mk_test_path "static_ABAcalls0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_ABAcalls1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_ABAcalls2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_ABAcalls3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_ABAcallsSuicide0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_ABAcallsSuicide1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_CALL_OneVCallSuicide.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_CALL_ZeroVCallSuicide.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_CREATE_ContractSuicideDuringInit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "static_CREATE_ContractSuicideDuringInit_ThenStoreThenReturn.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "static_CREATE_ContractSuicideDuringInit_WithValue.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_CREATE_EmptyContractAndCallIt_0wei.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "static_CREATE_EmptyContractWithStorageAndCallIt_0wei.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_Call10.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_Call1024BalanceTooLow.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_Call1024BalanceTooLow2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_Call1024OOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_Call1024PreCalls.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_Call1024PreCalls2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "static_Call1024PreCalls3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow *)
val test_path = mk_test_path "static_Call1MB1024Calldepth.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: slow *)
val test_path = mk_test_path "static_Call50000.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO add
static_Call50000_ecrec.json
static_Call50000_identity.json
static_Call50000_identity2.json
static_Call50000_rip160.json
static_Call50000bytesContract50_1.json
static_Call50000bytesContract50_2.json
static_Call50000bytesContract50_3.json
static_CallAndCallcodeConsumeMoreGasThenTransactionHas.json
static_CallAskMoreGasOnDepth2ThenTransactionHas.json
static_CallContractToCreateContractAndCallItOOG.json
static_CallContractToCreateContractOOG.json
static_CallContractToCreateContractOOGBonusGas.json
static_CallContractToCreateContractWhichWouldCreateContractIfCalled.json
static_CallEcrecover0.json
static_CallEcrecover0_0input.json
static_CallEcrecover0_Gas2999.json
static_CallEcrecover0_NoGas.json
static_CallEcrecover0_completeReturnValue.json
static_CallEcrecover0_gas3000.json
static_CallEcrecover0_overlappingInputOutput.json
static_CallEcrecover1.json
static_CallEcrecover2.json
static_CallEcrecover3.json
static_CallEcrecover80.json
static_CallEcrecoverCheckLength.json
static_CallEcrecoverCheckLengthWrongV.json
static_CallEcrecoverH_prefixed0.json
static_CallEcrecoverR_prefixed0.json
static_CallEcrecoverS_prefixed0.json
static_CallEcrecoverV_prefixed0.json
static_CallGoesOOGOnSecondLevel.json
static_CallGoesOOGOnSecondLevel2.json
static_CallIdentitiy_1.json
static_CallIdentity_1_nonzeroValue.json
static_CallIdentity_2.json
static_CallIdentity_3.json
static_CallIdentity_4.json
static_CallIdentity_4_gas17.json
static_CallIdentity_4_gas18.json
static_CallIdentity_5.json
static_CallLoseGasOOG.json
static_CallRecursiveBomb0.json
static_CallRecursiveBomb0_OOG_atMaxCallDepth.json
static_CallRecursiveBomb1.json
static_CallRecursiveBomb2.json
static_CallRecursiveBomb3.json
static_CallRecursiveBombLog.json
static_CallRecursiveBombLog2.json
static_CallRecursiveBombPreCall.json
static_CallRecursiveBombPreCall2.json
static_CallRipemd160_1.json
static_CallRipemd160_2.json
static_CallRipemd160_3.json
static_CallRipemd160_3_postfixed0.json
static_CallRipemd160_3_prefixed0.json
static_CallRipemd160_4.json
static_CallRipemd160_4_gas719.json
static_CallRipemd160_5.json
static_CallSha256_1.json
static_CallSha256_1_nonzeroValue.json
static_CallSha256_2.json
static_CallSha256_3.json
static_CallSha256_3_postfix0.json
static_CallSha256_3_prefix0.json
static_CallSha256_4.json
static_CallSha256_4_gas99.json
static_CallSha256_5.json
static_CallToNameRegistrator0.json
static_CallToReturn1.json
static_CalltoReturn2.json
static_CheckCallCostOOG.json
static_CheckOpcodes.json
static_CheckOpcodes2.json
static_CheckOpcodes3.json
static_CheckOpcodes4.json
static_CheckOpcodes5.json
static_ExecuteCallThatAskForeGasThenTrabsactionHas.json
static_InternalCallHittingGasLimit.json
static_InternalCallHittingGasLimit2.json
static_InternalCallStoreClearsOOG.json
static_LoopCallsDepthThenRevert.json
static_LoopCallsDepthThenRevert2.json
static_LoopCallsDepthThenRevert3.json
static_LoopCallsThenRevert.json
static_PostToReturn1.json
static_RETURN_Bounds.json
static_RETURN_BoundsOOG.json
static_RawCallGasAsk.json
static_Return50000_2.json
static_ReturnTest.json
static_ReturnTest2.json
static_RevertDepth2.json
static_RevertOpcodeCalls.json
static_ZeroValue_CALL_OOGRevert.json
static_ZeroValue_SUICIDE_OOGRevert.json
static_callBasic.json
static_callChangeRevert.json
static_callCreate.json
static_callCreate2.json
static_callCreate3.json
static_callOutput1.json
static_callOutput2.json
static_callOutput3.json
static_callOutput3Fail.json
static_callOutput3partial.json
static_callOutput3partialFail.json
static_callToCallCodeOpCodeCheck.json
static_callToCallOpCodeCheck.json
static_callToDelCallOpCodeCheck.json
static_callToStaticOpCodeCheck.json
static_callWithHighValue.json
static_callWithHighValueAndGasOOG.json
static_callWithHighValueAndOOGatTxLevel.json
static_callWithHighValueOOGinCall.json
static_call_OOG_additionalGasCosts1.json
static_call_OOG_additionalGasCosts2_Paris.json
static_call_value_inherit.json
static_call_value_inherit_from_call.json
static_callcall_00.json
static_callcall_00_OOGE.json
static_callcall_00_OOGE_1.json
static_callcall_00_OOGE_2.json
static_callcall_00_SuicideEnd.json
static_callcallcall_000.json
static_callcallcall_000_OOGE.json
static_callcallcall_000_OOGMAfter.json
static_callcallcall_000_OOGMAfter2.json
static_callcallcall_000_OOGMBefore.json
static_callcallcall_000_SuicideEnd.json
static_callcallcall_000_SuicideMiddle.json
static_callcallcall_ABCB_RECURSIVE.json
static_callcallcallcode_001.json
static_callcallcallcode_001_2.json
static_callcallcallcode_001_OOGE.json
static_callcallcallcode_001_OOGE_2.json
static_callcallcallcode_001_OOGMAfter.json
static_callcallcallcode_001_OOGMAfter2.json
static_callcallcallcode_001_OOGMAfter_2.json
static_callcallcallcode_001_OOGMAfter_3.json
static_callcallcallcode_001_OOGMBefore.json
static_callcallcallcode_001_OOGMBefore2.json
static_callcallcallcode_001_SuicideEnd.json
static_callcallcallcode_001_SuicideEnd2.json
static_callcallcallcode_001_SuicideMiddle.json
static_callcallcallcode_001_SuicideMiddle2.json
static_callcallcallcode_ABCB_RECURSIVE.json
static_callcallcallcode_ABCB_RECURSIVE2.json
static_callcallcode_01_2.json
static_callcallcode_01_OOGE_2.json
static_callcallcode_01_SuicideEnd.json
static_callcallcode_01_SuicideEnd2.json
static_callcallcodecall_010.json
static_callcallcodecall_010_2.json
static_callcallcodecall_010_OOGE.json
static_callcallcodecall_010_OOGE_2.json
static_callcallcodecall_010_OOGMAfter.json
static_callcallcodecall_010_OOGMAfter2.json
static_callcallcodecall_010_OOGMAfter_2.json
static_callcallcodecall_010_OOGMAfter_3.json
static_callcallcodecall_010_OOGMBefore.json
static_callcallcodecall_010_OOGMBefore2.json
static_callcallcodecall_010_SuicideEnd.json
static_callcallcodecall_010_SuicideEnd2.json
static_callcallcodecall_010_SuicideMiddle.json
static_callcallcodecall_010_SuicideMiddle2.json
static_callcallcodecall_ABCB_RECURSIVE.json
static_callcallcodecall_ABCB_RECURSIVE2.json
static_callcallcodecallcode_011.json
static_callcallcodecallcode_011_2.json
static_callcallcodecallcode_011_OOGE.json
static_callcallcodecallcode_011_OOGE_2.json
static_callcallcodecallcode_011_OOGMAfter.json
static_callcallcodecallcode_011_OOGMAfter2.json
static_callcallcodecallcode_011_OOGMAfter_1.json
static_callcallcodecallcode_011_OOGMAfter_2.json
static_callcallcodecallcode_011_OOGMBefore.json
static_callcallcodecallcode_011_OOGMBefore2.json
static_callcallcodecallcode_011_SuicideEnd.json
static_callcallcodecallcode_011_SuicideEnd2.json
static_callcallcodecallcode_011_SuicideMiddle.json
static_callcallcodecallcode_011_SuicideMiddle2.json
static_callcallcodecallcode_ABCB_RECURSIVE.json
static_callcallcodecallcode_ABCB_RECURSIVE2.json
static_callcode_checkPC.json
static_callcodecall_10.json
static_callcodecall_10_2.json
static_callcodecall_10_OOGE.json
static_callcodecall_10_OOGE_2.json
static_callcodecall_10_SuicideEnd.json
static_callcodecall_10_SuicideEnd2.json
static_callcodecallcall_100.json
static_callcodecallcall_100_2.json
static_callcodecallcall_100_OOGE.json
static_callcodecallcall_100_OOGE2.json
static_callcodecallcall_100_OOGMAfter.json
static_callcodecallcall_100_OOGMAfter2.json
static_callcodecallcall_100_OOGMAfter_2.json
static_callcodecallcall_100_OOGMAfter_3.json
static_callcodecallcall_100_OOGMBefore.json
static_callcodecallcall_100_OOGMBefore2.json
static_callcodecallcall_100_SuicideEnd.json
static_callcodecallcall_100_SuicideEnd2.json
static_callcodecallcall_100_SuicideMiddle.json
static_callcodecallcall_100_SuicideMiddle2.json
static_callcodecallcall_ABCB_RECURSIVE.json
static_callcodecallcall_ABCB_RECURSIVE2.json
static_callcodecallcallcode_101.json
static_callcodecallcallcode_101_2.json
static_callcodecallcallcode_101_OOGE.json
static_callcodecallcallcode_101_OOGE_2.json
static_callcodecallcallcode_101_OOGMAfter.json
static_callcodecallcallcode_101_OOGMAfter2.json
static_callcodecallcallcode_101_OOGMAfter_1.json
static_callcodecallcallcode_101_OOGMAfter_3.json
static_callcodecallcallcode_101_OOGMBefore.json
static_callcodecallcallcode_101_OOGMBefore2.json
static_callcodecallcallcode_101_SuicideEnd.json
static_callcodecallcallcode_101_SuicideEnd2.json
static_callcodecallcallcode_101_SuicideMiddle.json
static_callcodecallcallcode_101_SuicideMiddle2.json
static_callcodecallcallcode_ABCB_RECURSIVE.json
static_callcodecallcallcode_ABCB_RECURSIVE2.json
static_callcodecallcodecall_110.json
static_callcodecallcodecall_1102.json
static_callcodecallcodecall_110_2.json
static_callcodecallcodecall_110_OOGE.json
static_callcodecallcodecall_110_OOGE2.json
static_callcodecallcodecall_110_OOGMAfter.json
static_callcodecallcodecall_110_OOGMAfter2.json
static_callcodecallcodecall_110_OOGMAfter_2.json
static_callcodecallcodecall_110_OOGMAfter_3.json
static_callcodecallcodecall_110_OOGMBefore.json
static_callcodecallcodecall_110_OOGMBefore2.json
static_callcodecallcodecall_110_SuicideEnd.json
static_callcodecallcodecall_110_SuicideEnd2.json
static_callcodecallcodecall_110_SuicideMiddle.json
static_callcodecallcodecall_110_SuicideMiddle2.json
static_callcodecallcodecall_ABCB_RECURSIVE.json
static_callcodecallcodecall_ABCB_RECURSIVE2.json
static_callcodecallcodecallcode_111_SuicideEnd.json
static_calldelcode_01.json
static_calldelcode_01_OOGE.json
static_contractCreationMakeCallThatAskMoreGasThenTransactionProvided.json
static_contractCreationOOGdontLeaveEmptyContractViaTransaction.json
static_log0_emptyMem.json
static_log0_logMemStartTooHigh.json
static_log0_logMemsizeTooHigh.json
static_log0_logMemsizeZero.json
static_log0_nonEmptyMem.json
static_log0_nonEmptyMem_logMemSize1.json
static_log0_nonEmptyMem_logMemSize1_logMemStart31.json
static_log1_MaxTopic.json
static_log1_emptyMem.json
static_log1_logMemStartTooHigh.json
static_log1_logMemsizeTooHigh.json
static_log1_logMemsizeZero.json
static_log_Caller.json
static_makeMoney.json
static_refund_CallA.json
static_refund_CallToSuicideNoStorage.json
static_refund_CallToSuicideTwice.json
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stStaticFlagEnabled/" ^ s;

val test_path = mk_test_path "CallWithNOTZeroValueToPrecompileFromCalledContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "CallWithNOTZeroValueToPrecompileFromContractInitialization.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallWithNOTZeroValueToPrecompileFromTransaction.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: fix
val test_path = mk_test_path "CallWithZeroValueToPrecompileFromCalledContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: fix
val test_path = mk_test_path
  "CallWithZeroValueToPrecompileFromContractInitialization.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: fix
val test_path = mk_test_path "CallWithZeroValueToPrecompileFromTransaction.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: fix
val test_path = mk_test_path "CallcodeToPrecompileFromCalledContract.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: fix
val test_path = mk_test_path "CallcodeToPrecompileFromContractInitialization.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: fix - needs precompiles
val test_path = mk_test_path "CallcodeToPrecompileFromTransaction.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: add
DelegatecallToPrecompileFromCalledContract.json
DelegatecallToPrecompileFromContractInitialization.json
DelegatecallToPrecompileFromTransaction.json
StaticcallForPrecompilesIssue683.json
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stSystemOperationsTest/" ^ s;

val test_path = mk_test_path "ABAcalls0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ABAcalls1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ABAcalls2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ABAcalls3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ABAcallsSuicide0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ABAcallsSuicide1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "Call10.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallRecursiveBomb0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallRecursiveBomb0_OOG_atMaxCallDepth.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallRecursiveBomb1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallRecursiveBomb2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallRecursiveBomb3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallRecursiveBombLog.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallRecursiveBombLog2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToNameRegistrator0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToNameRegistratorAddressTooBigLeft.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToNameRegistratorAddressTooBigRight.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToNameRegistratorMemOOGAndInsufficientBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToNameRegistratorNotMuchMemory0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToNameRegistratorNotMuchMemory1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToNameRegistratorOutOfGas.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToNameRegistratorTooMuchMemory0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToNameRegistratorTooMuchMemory1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToNameRegistratorTooMuchMemory2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToNameRegistratorZeorSizeMemExpansion.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToReturn1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToReturn1ForDynamicJump0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CallToReturn1ForDynamicJump1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CalltoReturn2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateHashCollision.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "PostToReturn1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "TestNameRegistrator.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "balanceInputAddressTooBig.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callValue.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeTo0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeToNameRegistrator0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeToNameRegistratorAddresTooBigLeft.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeToNameRegistratorAddresTooBigRight.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeToNameRegistratorZeroMemExpanion.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callcodeToReturn1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "callerAccountBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistrator.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistratorOOG_MemExpansionOOV.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistratorOutOfMemoryBonds0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistratorOutOfMemoryBonds1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistratorValueTooHigh.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistratorZeroMem.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistratorZeroMem2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createNameRegistratorZeroMemExpansion.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "createWithInvalidOpcode.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "currentAccountBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "doubleSelfdestructTest.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "doubleSelfdestructTouch_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "extcodecopy.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "multiSelfdestruct.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "return0.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "return1.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "return2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "suicideAddress.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "suicideCaller.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "suicideCallerAddresTooBigLeft.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "suicideCallerAddresTooBigRight.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "suicideNotExistingAccount.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "suicideOrigin.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "suicideSendEtherPostDeath.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "suicideSendEtherToMe.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "testRandomTest.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stTimeConsuming/" ^ s;

(* TODO: add
CALLBlake2f_MaxRounds.json
sstore_combinations_initial00_2_Paris.json
sstore_combinations_initial00_Paris.json
sstore_combinations_initial01_2_Paris.json
sstore_combinations_initial01_Paris.json
sstore_combinations_initial10_2_Paris.json
sstore_combinations_initial10_Paris.json
sstore_combinations_initial11_2_Paris.json
sstore_combinations_initial11_Paris.json
sstore_combinations_initial20_2_Paris.json
sstore_combinations_initial20_Paris.json
sstore_combinations_initial21_2_Paris.json
sstore_combinations_initial21_Paris.json
static_Call50000_sha256.json
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stTransactionTest/" ^ s;

val test_path = mk_test_path "ContractStoreClearsOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ContractStoreClearsSuccess.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateMessageReverted.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateMessageSuccess.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "CreateTransactionSuccess.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "EmptyTransaction3.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "HighGasLimit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "HighGasPriceParis.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "InternalCallHittingGasLimit.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "InternalCallHittingGasLimit2.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "InternalCallHittingGasLimitSuccess.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "InternalCallStoreClearsOOG.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "InternalCallStoreClearsSuccess.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: parse
val test_path = mk_test_path "NoSrcAccount.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);
*)

(* TODO: add
NoSrcAccount1559.json
NoSrcAccountCreate.json
NoSrcAccountCreate1559.json
Opcodes_TransactionInit.json
OverflowGasRequire2.json
PointAtInfinityECRecover.json
StoreClearsAndInternalCallStoreClearsOOG.json
StoreClearsAndInternalCallStoreClearsSuccess.json
StoreGasOnCreate.json
SuicidesAndInternalCallSuicidesBonusGasAtCall.json
SuicidesAndInternalCallSuicidesBonusGasAtCallFailed.json
SuicidesAndInternalCallSuicidesOOG.json
SuicidesAndInternalCallSuicidesSuccess.json
SuicidesAndSendMoneyToItselfEtherDestroyed.json
SuicidesStopAfterSuicide.json
TransactionDataCosts652.json
TransactionSendingToEmpty.json
TransactionSendingToZero.json
TransactionToAddressh160minusOne.json
TransactionToItself.json
ValueOverflowParis.json
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stTransitionTest/" ^ s;

(* TODO: add
createNameRegistratorPerTxsAfter.json
createNameRegistratorPerTxsAt.json
createNameRegistratorPerTxsBefore.json
delegatecallAfterTransition.json
delegatecallAtTransition.json
delegatecallBeforeTransition.json
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stWalletTest/" ^ s;

(* TODO: better handle transactions with lots of data *)
val test_path = mk_test_path "dayLimitConstruction.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

(* TODO: add
dayLimitConstructionOOG.json
dayLimitConstructionPartial.json
dayLimitResetSpentToday.json
dayLimitSetDailyLimit.json
dayLimitSetDailyLimitNoData.json
multiOwnedAddOwner.json
multiOwnedAddOwnerAddMyself.json
multiOwnedChangeOwner.json
multiOwnedChangeOwnerNoArgument.json
multiOwnedChangeOwner_fromNotOwner.json
multiOwnedChangeOwner_toIsOwner.json
multiOwnedChangeRequirementTo0.json
multiOwnedChangeRequirementTo1.json
multiOwnedChangeRequirementTo2.json
multiOwnedConstructionCorrect.json
multiOwnedConstructionNotEnoughGas.json
multiOwnedConstructionNotEnoughGasPartial.json
multiOwnedIsOwnerFalse.json
multiOwnedIsOwnerTrue.json
multiOwnedRemoveOwner.json
multiOwnedRemoveOwnerByNonOwner.json
multiOwnedRemoveOwner_mySelf.json
multiOwnedRemoveOwner_ownerIsNotOwner.json
multiOwnedRevokeNothing.json
walletAddOwnerRemovePendingTransaction.json
walletChangeOwnerRemovePendingTransaction.json
walletChangeRequirementRemovePendingTransaction.json
walletConfirm.json
walletConstruction.json
walletConstructionOOG.json
walletConstructionPartial.json
walletDefault.json
walletDefaultWithOutValue.json
walletExecuteOverDailyLimitMultiOwner.json
walletExecuteOverDailyLimitOnlyOneOwner.json
walletExecuteOverDailyLimitOnlyOneOwnerNew.json
walletExecuteUnderDailyLimit.json
walletKill.json
walletKillNotByOwner.json
walletKillToWallet.json
walletRemoveOwnerRemovePendingTransaction.json
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stZeroCallsRevert/" ^ s;

(* TODO: add
ZeroValue_CALLCODE_OOGRevert.json
ZeroValue_CALLCODE_ToEmpty_OOGRevert_Paris.json
ZeroValue_CALLCODE_ToNonZeroBalance_OOGRevert.json
ZeroValue_CALLCODE_ToOneStorageKey_OOGRevert_Paris.json
ZeroValue_CALL_OOGRevert.json
ZeroValue_CALL_ToEmpty_OOGRevert_Paris.json
ZeroValue_CALL_ToNonZeroBalance_OOGRevert.json
ZeroValue_CALL_ToOneStorageKey_OOGRevert_Paris.json
ZeroValue_DELEGATECALL_OOGRevert.json
ZeroValue_DELEGATECALL_ToEmpty_OOGRevert_Paris.json
ZeroValue_DELEGATECALL_ToNonZeroBalance_OOGRevert.json
ZeroValue_DELEGATECALL_ToOneStorageKey_OOGRevert_Paris.json
ZeroValue_SUICIDE_OOGRevert.json
ZeroValue_SUICIDE_ToEmpty_OOGRevert_Paris.json
ZeroValue_SUICIDE_ToNonZeroBalance_OOGRevert.json
ZeroValue_SUICIDE_ToOneStorageKey_OOGRevert_Paris.json
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stZeroCallsTest/" ^ s;

val test_path = mk_test_path "ZeroValue_CALL.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_CALLCODE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_CALLCODE_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_CALLCODE_ToNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_CALLCODE_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_CALL_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_CALL_ToNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_CALL_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_DELEGATECALL.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_DELEGATECALL_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_DELEGATECALL_ToNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_DELEGATECALL_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_SUICIDE.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_SUICIDE_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_SUICIDE_ToNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_SUICIDE_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_TransactionCALL.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_TransactionCALL_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_TransactionCALL_ToNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_TransactionCALL_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_TransactionCALLwithData.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_TransactionCALLwithData_ToEmpty_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path "ZeroValue_TransactionCALLwithData_ToNonZeroBalance.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

val test_path = mk_test_path
  "ZeroValue_TransactionCALLwithData_ToOneStorageKey_Paris.json";
val (num_tests, prove_test) = mk_prove_test test_path;
val thms = List.tabulate (num_tests, prove_test);

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stZeroKnowledge/" ^ s;

(* TODO: add
ecmul_1-2_2_28000_128.json
ecmul_1-2_2_28000_96.json
ecmul_1-2_340282366920938463463374607431768211456_21000_128.json
ecmul_1-2_340282366920938463463374607431768211456_21000_80.json
ecmul_1-2_340282366920938463463374607431768211456_21000_96.json
ecmul_1-2_340282366920938463463374607431768211456_28000_128.json
ecmul_1-2_340282366920938463463374607431768211456_28000_80.json
ecmul_1-2_340282366920938463463374607431768211456_28000_96.json
ecmul_1-2_5616_21000_128.json
ecmul_1-2_5616_21000_96.json
ecmul_1-2_5616_28000_128.json
ecmul_1-2_5617_21000_128.json
ecmul_1-2_5617_21000_96.json
ecmul_1-2_5617_28000_128.json
ecmul_1-2_5617_28000_96.json
ecmul_1-2_616_28000_96.json
ecmul_1-2_9935_21000_128.json
ecmul_1-2_9935_21000_96.json
ecmul_1-2_9935_28000_128.json
ecmul_1-2_9935_28000_96.json
ecmul_1-2_9_21000_128.json
ecmul_1-2_9_21000_96.json
ecmul_1-2_9_28000_128.json
ecmul_1-2_9_28000_96.json
ecmul_1-3_0_21000_128.json
ecmul_1-3_0_21000_64.json
ecmul_1-3_0_21000_80.json
ecmul_1-3_0_21000_96.json
ecmul_1-3_0_28000_128.json
ecmul_1-3_0_28000_64.json
ecmul_1-3_0_28000_80_Paris.json
ecmul_1-3_0_28000_96.json
ecmul_1-3_1_21000_128.json
ecmul_1-3_1_21000_96.json
ecmul_1-3_1_28000_128.json
ecmul_1-3_1_28000_96.json
ecmul_1-3_2_21000_128.json
ecmul_1-3_2_21000_96.json
ecmul_1-3_2_28000_128.json
ecmul_1-3_2_28000_96.json
ecmul_1-3_340282366920938463463374607431768211456_21000_128.json
ecmul_1-3_340282366920938463463374607431768211456_21000_80.json
ecmul_1-3_340282366920938463463374607431768211456_21000_96.json
ecmul_1-3_340282366920938463463374607431768211456_28000_128.json
ecmul_1-3_340282366920938463463374607431768211456_28000_80.json
ecmul_1-3_340282366920938463463374607431768211456_28000_96.json
ecmul_1-3_5616_21000_128.json
ecmul_1-3_5616_21000_96.json
ecmul_1-3_5616_28000_128.json
ecmul_1-3_5616_28000_96.json
ecmul_1-3_5617_21000_128.json
ecmul_1-3_5617_21000_96.json
ecmul_1-3_5617_28000_128.json
ecmul_1-3_5617_28000_96.json
ecmul_1-3_9935_21000_128.json
ecmul_1-3_9935_21000_96.json
ecmul_1-3_9935_28000_128.json
ecmul_1-3_9935_28000_96.json
ecmul_1-3_9_21000_128.json
ecmul_1-3_9_21000_96.json
ecmul_1-3_9_28000_128.json
ecmul_1-3_9_28000_96.json
ecmul_7827-6598_0_21000_128.json
ecmul_7827-6598_0_21000_64.json
ecmul_7827-6598_0_21000_80.json
ecmul_7827-6598_0_21000_96.json
ecmul_7827-6598_0_28000_128.json
ecmul_7827-6598_0_28000_64.json
ecmul_7827-6598_0_28000_80.json
ecmul_7827-6598_0_28000_96.json
ecmul_7827-6598_1456_21000_128.json
ecmul_7827-6598_1456_21000_80.json
ecmul_7827-6598_1456_21000_96.json
ecmul_7827-6598_1456_28000_128.json
ecmul_7827-6598_1456_28000_80.json
ecmul_7827-6598_1456_28000_96.json
ecmul_7827-6598_1_21000_128.json
ecmul_7827-6598_1_21000_96.json
ecmul_7827-6598_1_28000_128.json
ecmul_7827-6598_1_28000_96.json
ecmul_7827-6598_2_21000_128.json
ecmul_7827-6598_2_21000_96.json
ecmul_7827-6598_2_28000_128.json
ecmul_7827-6598_2_28000_96.json
ecmul_7827-6598_5616_21000_128.json
ecmul_7827-6598_5616_21000_96.json
ecmul_7827-6598_5616_28000_128.json
ecmul_7827-6598_5616_28000_96.json
ecmul_7827-6598_5617_21000_128.json
ecmul_7827-6598_5617_21000_96.json
ecmul_7827-6598_5617_28000_128.json
ecmul_7827-6598_5617_28000_96.json
ecmul_7827-6598_9935_21000_128.json
ecmul_7827-6598_9935_21000_96.json
ecmul_7827-6598_9935_28000_128.json
ecmul_7827-6598_9935_28000_96.json
ecmul_7827-6598_9_21000_128.json
ecmul_7827-6598_9_21000_96.json
ecmul_7827-6598_9_28000_128.json
ecmul_7827-6598_9_28000_96.json
ecpairing_bad_length_191.json
ecpairing_bad_length_193.json
ecpairing_empty_data.json
ecpairing_empty_data_insufficient_gas.json
ecpairing_inputs.json
ecpairing_one_point_fail.json
ecpairing_one_point_insufficient_gas.json
ecpairing_one_point_not_in_subgroup.json
ecpairing_one_point_with_g1_zero.json
ecpairing_one_point_with_g2_zero.json
ecpairing_one_point_with_g2_zero_and_g1_invalid.json
ecpairing_perturb_g2_by_curve_order.json
ecpairing_perturb_g2_by_field_modulus.json
ecpairing_perturb_g2_by_field_modulus_again.json
ecpairing_perturb_g2_by_one.json
ecpairing_perturb_zeropoint_by_curve_order.json
ecpairing_perturb_zeropoint_by_field_modulus.json
ecpairing_perturb_zeropoint_by_one.json
ecpairing_three_point_fail_1.json
ecpairing_three_point_match_1.json
ecpairing_two_point_fail_1.json
ecpairing_two_point_fail_2.json
ecpairing_two_point_match_1.json
ecpairing_two_point_match_2.json
ecpairing_two_point_match_3.json
ecpairing_two_point_match_4.json
ecpairing_two_point_match_5.json
ecpairing_two_point_oog.json
ecpairing_two_points_with_one_g2_zero.json
pairingTest.json
pointAdd.json
pointAddTrunc.json
pointMulAdd.json
pointMulAdd2.json
*)

fun mk_test_path s =
  "tests/BlockchainTests/GeneralStateTests/stZeroKnowledge2/" ^ s;

(* TODO add
ecadd_0-0_0-0_21000_0.json
ecadd_0-0_0-0_21000_128.json
ecadd_0-0_0-0_21000_192.json
ecadd_0-0_0-0_21000_64.json
ecadd_0-0_0-0_21000_80_Paris.json
ecadd_0-0_0-0_25000_0.json
ecadd_0-0_0-0_25000_128.json
ecadd_0-0_0-0_25000_192.json
ecadd_0-0_0-0_25000_64.json
ecadd_0-0_0-0_25000_80.json
ecadd_0-0_1-2_21000_128.json
ecadd_0-0_1-2_21000_192.json
ecadd_0-0_1-2_25000_128.json
ecadd_0-0_1-2_25000_192.json
ecadd_0-0_1-3_21000_128.json
ecadd_0-0_1-3_25000_128.json
ecadd_0-3_1-2_21000_128.json
ecadd_0-3_1-2_25000_128.json
ecadd_1-2_0-0_21000_128.json
ecadd_1-2_0-0_21000_192.json
ecadd_1-2_0-0_21000_64.json
ecadd_1-2_0-0_25000_128.json
ecadd_1-2_0-0_25000_192.json
ecadd_1-2_0-0_25000_64.json
ecadd_1-2_1-2_21000_128.json
ecadd_1-2_1-2_21000_192.json
ecadd_1-2_1-2_25000_128.json
ecadd_1-2_1-2_25000_192.json
ecadd_1-3_0-0_21000_80.json
ecadd_1-3_0-0_25000_80_Paris.json
ecadd_1145-3932_1145-4651_21000_192.json
ecadd_1145-3932_1145-4651_25000_192.json
ecadd_1145-3932_2969-1336_21000_128.json
ecadd_1145-3932_2969-1336_25000_128.json
ecadd_6-9_19274124-124124_21000_128.json
ecadd_6-9_19274124-124124_25000_128.json
ecmul_0-0_0_21000_0.json
ecmul_0-0_0_21000_128.json
ecmul_0-0_0_21000_40.json
ecmul_0-0_0_21000_64.json
ecmul_0-0_0_21000_80.json
ecmul_0-0_0_21000_96.json
ecmul_0-0_0_28000_0.json
ecmul_0-0_0_28000_128.json
ecmul_0-0_0_28000_40.json
ecmul_0-0_0_28000_64.json
ecmul_0-0_0_28000_80.json
ecmul_0-0_0_28000_96.json
ecmul_0-0_1_21000_128.json
ecmul_0-0_1_21000_96.json
ecmul_0-0_1_28000_128.json
ecmul_0-0_1_28000_96.json
ecmul_0-0_2_21000_128.json
ecmul_0-0_2_21000_96.json
ecmul_0-0_2_28000_128.json
ecmul_0-0_2_28000_96.json
ecmul_0-0_340282366920938463463374607431768211456_21000_128.json
ecmul_0-0_340282366920938463463374607431768211456_21000_80.json
ecmul_0-0_340282366920938463463374607431768211456_21000_96.json
ecmul_0-0_340282366920938463463374607431768211456_28000_128.json
ecmul_0-0_340282366920938463463374607431768211456_28000_80.json
ecmul_0-0_340282366920938463463374607431768211456_28000_96.json
ecmul_0-0_5616_21000_128.json
ecmul_0-0_5616_21000_96.json
ecmul_0-0_5616_28000_128.json
ecmul_0-0_5616_28000_96.json
ecmul_0-0_5617_21000_128.json
ecmul_0-0_5617_21000_96.json
ecmul_0-0_5617_28000_128.json
ecmul_0-0_5617_28000_96.json
ecmul_0-0_9935_21000_128.json
ecmul_0-0_9935_21000_96.json
ecmul_0-0_9935_28000_128.json
ecmul_0-0_9935_28000_96.json
ecmul_0-0_9_21000_128.json
ecmul_0-0_9_21000_96.json
ecmul_0-0_9_28000_128.json
ecmul_0-0_9_28000_96.json
ecmul_0-3_0_21000_128.json
ecmul_0-3_0_21000_64.json
ecmul_0-3_0_21000_80.json
ecmul_0-3_0_21000_96.json
ecmul_0-3_0_28000_128.json
ecmul_0-3_0_28000_64.json
ecmul_0-3_0_28000_80.json
ecmul_0-3_0_28000_96.json
ecmul_0-3_1_21000_128.json
ecmul_0-3_1_21000_96.json
ecmul_0-3_1_28000_128.json
ecmul_0-3_1_28000_96.json
ecmul_0-3_2_21000_128.json
ecmul_0-3_2_21000_96.json
ecmul_0-3_2_28000_128.json
ecmul_0-3_2_28000_96.json
ecmul_0-3_340282366920938463463374607431768211456_21000_128.json
ecmul_0-3_340282366920938463463374607431768211456_21000_80.json
ecmul_0-3_340282366920938463463374607431768211456_21000_96.json
ecmul_0-3_340282366920938463463374607431768211456_28000_128.json
ecmul_0-3_340282366920938463463374607431768211456_28000_80.json
ecmul_0-3_340282366920938463463374607431768211456_28000_96.json
ecmul_0-3_5616_21000_128.json
ecmul_0-3_5616_21000_96.json
ecmul_0-3_5616_28000_128.json
ecmul_0-3_5616_28000_96_Paris.json
ecmul_0-3_5617_21000_128.json
ecmul_0-3_5617_21000_96.json
ecmul_0-3_5617_28000_128.json
ecmul_0-3_5617_28000_96.json
ecmul_0-3_9935_21000_128.json
ecmul_0-3_9935_21000_96.json
ecmul_0-3_9935_28000_128.json
ecmul_0-3_9935_28000_96.json
ecmul_0-3_9_21000_128.json
ecmul_0-3_9_21000_96.json
ecmul_0-3_9_28000_128.json
ecmul_0-3_9_28000_96.json
ecmul_1-2_0_21000_128.json
ecmul_1-2_0_21000_64.json
ecmul_1-2_0_21000_80.json
ecmul_1-2_0_21000_96.json
ecmul_1-2_0_28000_128.json
ecmul_1-2_0_28000_64.json
ecmul_1-2_0_28000_80.json
ecmul_1-2_0_28000_96.json
ecmul_1-2_1_21000_128.json
ecmul_1-2_1_21000_96.json
ecmul_1-2_1_28000_128.json
ecmul_1-2_1_28000_96.json
ecmul_1-2_2_21000_128.json
ecmul_1-2_2_21000_96.json
*)

(*
val _ = (cv_memLib.verbosity_level := cv_memLib.Verbose);

cv_eval_raw ``
let acc = modexp_d28g0v0_Cancun_pre in
let blk = modexp_d28g0v0_Cancun_block in
let tx = modexp_d28g0v0_Cancun_transaction in
let init = run_create 1 [] blk acc tx in
let cont = OUTR $ THE init in
let s = SND cont in
let (r, s) = run_n 12 s in
let c = EL 0 s.contexts in
  (ISL r, LENGTH s.contexts,
   c.stack,
   c.gasUsed,
   c.callParams.gasLimit,
   (c.addRefund, c.subRefund),
   c.jumpDest,
   FLOOKUP c.callParams.parsed c.pc,
   LENGTH c.memory,
   c.memory,
   c.callParams.static,
   c.callParams.callee,
   (lookup_account c.callParams.callee s.accounts).nonce,
   (lookup_storage 0w (lookup_account c.callParams.callee s.accounts).storage),
   (lookup_storage 1w (lookup_account c.callParams.callee s.accounts).storage)
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
