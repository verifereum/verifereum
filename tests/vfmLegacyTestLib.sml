structure vfmLegacyTestLib :> vfmLegacyTestLib = struct

open HolKernel boolLib bossLib Parse
     wordsLib permLib cv_transLib readTestJsonLib
     listTheory pairTheory optionTheory combinTheory
     cvTheory cv_typeTheory cv_stdTheory
     vfmStateTheory vfmContextTheory vfmExecutionTheory
     vfmComputeTheory vfmTestHelperTheory

val export_theory_no_docs = fn () =>
  Feedback.set_trace "TheoryPP.include_docs" 0
  before export_theory ();

val run_block_pat = run_block_def |> SPEC_ALL |> concl |> lhs;

val run_block = run_block_pat |> strip_comb |> fst;

val cv_eval_run_block_rwts = [
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
  to_vfmContext_rollback_state_def,
  to_vfmContext_message_parameters_def,
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

val empty_accs_str = "(Collect empty_domain)"

fun mk_statement isHash test_name prev_hashes =
  if isHash then
    Term[QUOTE(String.concat[
           "∃n1 dom. run_blocks_to_hash n1 ", empty_accs_str, " 1 [",
           String.concatWith "; " (map (fn hash => "n2w " ^ hash) prev_hashes),
           "] ",
           test_name, "_pre ",
           test_name, "_blocks ",
           "= SOME (", test_name, "_post, dom)"])]
  else
    Term[QUOTE(String.concat[
           "∃rs prevhashes dom. run_blocks ", empty_accs_str, " 1 [",
           String.concatWith "; " (map (fn hash => "n2w " ^ hash) prev_hashes),
           "] ",
           test_name, "_pre ",
           test_name, "_blocks ",
           "= SOME (rs, prevhashes, ",
           test_name, "_post, dom)"])]

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

fun word_w2n_lt t1 t2 = let
  val n1 = t1 |> rand |> numSyntax.dest_numeral
  val n2 = t2 |> rand |> numSyntax.dest_numeral
in Arbnum.< (n1, n2) end

(*
  set_goal([], thm_term)
*)

val mk_tactic =
  CONV_TAC(STRIP_QUANT_CONV(LAND_CONV cv_eval_raw))
  \\ rewrite_tac cv_eval_run_block_rwts
  \\ rewrite_tac[LET_THM]
  \\ CONV_TAC(ONCE_DEPTH_CONV (BETA_CONV THENC EVAL))
  \\ rewrite_tac[SOME_11, PAIR_EQ]
  \\ rewrite_tac[unwind_lemma]
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

val mk_tactic_hash =
  exists_tac trie_n
  \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV cv_eval_raw))
  \\ rewrite_tac[to_option_def, SOME_11, to_pair_def, PAIR_EQ]
  \\ rewrite_tac[unwind_lemma2]
  \\ EVAL_TAC

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

  val SOME test_index = findIndexByName "randomStatetest108" test_names
*)

fun prep_test test_path test_index = let
  val test_names = get_test_names test_path;
  val test_name = List.nth(test_names, test_index);
  val test_name_escaped =
    let
      val e = String.translate remove_special_chars test_name
    in
      if Char.isDigit $ String.sub (e, 0) then "t" ^ e else e
    end
  val test = get_test test_path test_name;
  val isHash = not $ Option.isSome $ #post test;

  val blocks = #blocks test;

  (* initialize prev_hashes with "parentHash" of 0th block *)
  val prev_hashes = [#parentHash (List.nth (blocks, 0))]

  fun tx_term block transaction =
    String.concat[
      "<| from := n2w ", #sender transaction,
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
      ";accessList := ", accesses_term $ #accessList transaction,
      ";blobVersionedHashes := [] ", (* TODO: include blobs if in test *)
      ";blobGasPrice := 0 ", (* TODO: calculate if excess_blob_gas is in test *)
      " |>"
    ];

  fun blk_term block =
    String.concat[
      "<| number := ", #number block,
      ";baseFeePerGas := ", #baseFeePerGas block,
      ";timeStamp := ", #timeStamp block,
      ";coinBase := n2w ", #coinBase block,
      ";hash := n2w ", #hash block,
      ";gasLimit := ", #gasLimit block,
      ";prevRandao := n2w ", #prevRandao block,
      ";parentBeaconBlockRoot := n2w ", #parentBeaconBlockRoot block,
      ";transactions := [",
      String.concatWith ";" (map (tx_term block) (#transactions block)),
      "]",
      "|>"
    ];


  val blocks_def = new_definition(
    test_name_escaped ^ "_blocks_def",
    Term[QUOTE(String.concat[
    test_name_escaped, "_blocks = [",
    String.concatWith ";" (map blk_term blocks),
    "]"
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
  val () = cv_auto_trans blocks_def;
  val () = computeLib.add_funs [pre_def, post_def, blocks_def]
  val () = computeLib.add_funs code_defs;

  val thm_name = test_name_escaped ^ "_correctness";
  val thm_term = mk_statement isHash test_name_escaped prev_hashes;

  in (thm_name, thm_term, (if isHash then mk_tactic_hash else mk_tactic))
end

fun mk_prove_test test_path = let
  val test_names = get_test_names test_path;
  fun prove_test test_path test_index = let
    val x = prep_test test_path test_index
  in store_thm x end
in (List.length test_names, prove_test test_path) end

end
