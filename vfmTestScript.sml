open HolKernel boolLib bossLib Parse wordsLib dep_rewrite
     arithmeticTheory combinTheory whileTheory
     vfmTypesTheory vfmExecutionTheory
     vfmStateTheory vfmContextTheory
     vfmOperationTheory vfmComputeTheory
     readTestJsonLib
     cv_transLib cv_stdTheory cv_computeLib
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
  run s = SOME z ⇔
  (∃n t. run_n n s = (INR z, t) ∧
         ∀m. m < n ⇒ ISL (FST (run_n m s)))
Proof
  rw[run_def, run_n_def, EQ_IMP_THM]
  >- (
    imp_res_tac OWHILE_WHILE
    \\ imp_res_tac OWHILE_ENDCOND
    \\ qmatch_assum_rename_tac `~_ p`
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
  \\ conj_asm1_tac >- ( qexists_tac`n` \\ gs[] )
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- metis_tac[]
  \\ rw[]
  \\ qmatch_goalsub_rename_tac`FUNPOW _ m`
  \\ Cases_on`m < n` >- metis_tac[sumTheory.NOT_ISR_ISL]
  \\ Cases_on`n < m` >- metis_tac[SIMP_CONV std_ss [] ``ISL (INR _)``, pairTheory.FST]
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

Definition refund_fee_def:
  refund_fee (sender: address) refund accounts : evm_accounts =
  (sender =+ accounts sender with balance updated_by $+ refund) accounts
End

val () = refund_fee_def |>
  ONCE_REWRITE_RULE[GSYM lookup_account_def] |>
  ONCE_REWRITE_RULE[GSYM update_account_def] |>
  cv_auto_trans;

(*
https://github.com/ethereum/tests
commit 08839f5 (taken from the develop branch)
BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json
*)

open cv_typeTheory cvTheory

fun cv_eval_run_with_fuel_tac (goal as (_, gt)) = let
  val run_tm = find_term (can (match_term ``run_with_fuel _ _``)) gt
  val raw_th = cv_eval_raw run_tm
  val raw_th2 = raw_th |>
  REWRITE_RULE[
    cv_typeTheory.to_option_def,
    cv_typeTheory.to_pair_def,
    to_vfmExecution_outcome_def,
    cv_typeTheory.cv_has_shape_def,
    cvTheory.Num_11,
    EVAL``2n = 0``,
    EVAL``2n = 1``,
    EVAL``1n = 0``,
    to_vfmExecution_result_def,
    to_evm_accounts_def,
    cv_typeTheory.to_list_def,
    cvTheory.cv_fst_def,
    cvTheory.cv_snd_def,
    cvTheory.c2n_def,
    to_vfmContext_transaction_state_def,
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
  rewrite_tac[UNDISCH raw_th2]
end goal;

Definition update_beacon_block_def:
  update_beacon_block b accounts =
  let addr = 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02w in
  let buffer_length = 8191n in
  let timestamp_idx = b.timeStamp MOD buffer_length in
  let root_idx = timestamp_idx + buffer_length in
  let a = lookup_account accounts addr in
  let s0 = a.storage in
  let s1 = update_storage s0 (n2w timestamp_idx) (n2w b.timeStamp) in
  let s2 = update_storage s1 (n2w root_idx) b.parentBeaconBlockRoot in
  update_account accounts addr $ a with storage := s2
End

val () = cv_auto_trans update_beacon_block_def;

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

val test_path = "tests/add.json";
val test_names = get_test_names test_path;
val test_name = el 1 test_names;
val test = get_test test_path test_name;

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
    "|>"
  ])]);

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

Theorem add_d0g0v0_Cancun_correctness:
  ∃s r.
    initial_state 1
      add_d0g0v0_Cancun_pre
      add_d0g0v0_Cancun_block
      (Memory <| offset := 0; size := 0 |>)
      add_d0g0v0_Cancun_transaction = SOME s ∧
    run s = SOME (Finished r) ∧
    update_beacon_block add_d0g0v0_Cancun_block $ (* TODO: proper block processing *)
    refund_fee
      add_d0g0v0_Cancun_transaction.from
      (* TODO: refund should be limited by gas used / 5 *)
      (add_d0g0v0_Cancun_block.baseFeePerGas * (r.refund + r.gasLeft))
      r.accounts
    = add_d0g0v0_Cancun_post
Proof
  rw[run_SOME_run_n, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`SOME _ = s`
  \\ `s <> NONE` by ( qunabbrev_tac`s` \\ cv_eval_match_tac``_``)
  \\ `∃n z t.
        run_with_fuel n (INL (), THE s) = SOME (Finished z, t, 0) ∧
        update_beacon_block add_d0g0v0_Cancun_block $
        refund_fee
          add_d0g0v0_Cancun_transaction.from
          (add_d0g0v0_Cancun_block.baseFeePerGas * (z.refund + z.gasLeft))
          z.accounts = add_d0g0v0_Cancun_post`
      suffices_by (
    strip_tac
    \\ Cases_on`s` \\ gs[]
    \\ drule run_with_fuel_to_zero
    \\ strip_tac
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gs[] )
  \\ qunabbrev_tac`s`
  \\ qmatch_asmsub_abbrev_tac`Memory m`
  \\ `m = memory_range 0 0` by (rw[Abbr`m`] \\ cv_eval_match_tac``_``)
  \\ fs[Abbr`m`]
  \\ qexists_tac`18`
  \\ cv_eval_run_with_fuel_tac
  \\ simp[] \\ EVAL_TAC
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM] \\ rw[] \\ gs[]
  \\ gs[account_state_component_equality, FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[] \\ gs[]
  \\ EVAL_TAC
QED

val test_name = el 2 test_names;
val test = get_test test_path test_name;

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
    "|>"
  ])]);

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

(*

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

Theorem add_d1g0v0_Cancun_correctness:
  ∃s r.
    initial_state 1
      add_d1g0v0_Cancun_pre
      add_d1g0v0_Cancun_block
      (Memory <| offset := 0; size := 0 |>)
      add_d1g0v0_Cancun_transaction = SOME s ∧
    run s = SOME (Finished r) ∧
    update_beacon_block add_d1g0v0_Cancun_block $ (* TODO: proper block processing *)
    refund_fee
      add_d1g0v0_Cancun_transaction.from
      (* TODO: refund should be limited by gas used / 5 *)
      (add_d1g0v0_Cancun_block.baseFeePerGas * (r.refund + r.gasLeft))
      r.accounts
    = add_d1g0v0_Cancun_post
Proof
  rw[run_SOME_run_n, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`SOME _ = s`
  \\ `s <> NONE` by ( qunabbrev_tac`s` \\ cv_eval_match_tac``_``)
  \\ `∃n z t.
        run_with_fuel n (INL (), THE s) = SOME (Finished z, t, 0) ∧
        update_beacon_block add_d1g0v0_Cancun_block $
        refund_fee
          add_d1g0v0_Cancun_transaction.from
          (add_d1g0v0_Cancun_block.baseFeePerGas * (z.refund + z.gasLeft))
          z.accounts = add_d1g0v0_Cancun_post`
      suffices_by (
    strip_tac
    \\ Cases_on`s` \\ gs[]
    \\ drule run_with_fuel_to_zero
    \\ strip_tac
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gs[] )
  \\ qunabbrev_tac`s`
  \\ qmatch_asmsub_abbrev_tac`Memory m`
  \\ `m = memory_range 0 0` by (rw[Abbr`m`] \\ cv_eval_match_tac``_``)
  \\ fs[Abbr`m`]
  \\ qexists_tac`18`
  \\ cv_eval_run_with_fuel_tac
  \\ simp[] \\ EVAL_TAC
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM] \\ rw[] \\ gs[]
  \\ gs[account_state_component_equality, FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[] \\ gs[]
  \\ EVAL_TAC
QED

val test_name = el 3 test_names;
val test = get_test test_path test_name;

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
    "|>"
  ])]);

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

Theorem add_d2g0v0_Cancun_correctness:
  ∃s r.
    initial_state 1
      add_d2g0v0_Cancun_pre
      add_d2g0v0_Cancun_block
      (Memory <| offset := 0; size := 0 |>)
      add_d2g0v0_Cancun_transaction = SOME s ∧
    run s = SOME (Finished r) ∧
    update_beacon_block add_d2g0v0_Cancun_block $ (* TODO: proper block processing *)
    refund_fee
      add_d2g0v0_Cancun_transaction.from
      (* TODO: refund should be limited by gas used / 5 *)
      (add_d2g0v0_Cancun_block.baseFeePerGas * (r.refund + r.gasLeft))
      r.accounts
    = add_d2g0v0_Cancun_post
Proof
  rw[run_SOME_run_n, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`SOME _ = s`
  \\ `s <> NONE` by ( qunabbrev_tac`s` \\ cv_eval_match_tac``_``)
  \\ `∃n z t.
        run_with_fuel n (INL (), THE s) = SOME (Finished z, t, 0) ∧
        update_beacon_block add_d2g0v0_Cancun_block $
        refund_fee
          add_d2g0v0_Cancun_transaction.from
          (add_d2g0v0_Cancun_block.baseFeePerGas * (z.refund + z.gasLeft))
          z.accounts = add_d2g0v0_Cancun_post`
      suffices_by (
    strip_tac
    \\ Cases_on`s` \\ gs[]
    \\ drule run_with_fuel_to_zero
    \\ strip_tac
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gs[] )
  \\ qunabbrev_tac`s`
  \\ qmatch_asmsub_abbrev_tac`Memory m`
  \\ `m = memory_range 0 0` by (rw[Abbr`m`] \\ cv_eval_match_tac``_``)
  \\ fs[Abbr`m`]
  \\ qexists_tac`18`
  \\ cv_eval_run_with_fuel_tac
  \\ simp[] \\ EVAL_TAC
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM] \\ rw[] \\ gs[]
  \\ gs[account_state_component_equality, FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[] \\ gs[]
  \\ EVAL_TAC
QED

val test_name = el 4 test_names;
val test = get_test test_path test_name;

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
    "|>"
  ])]);

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

Theorem add_d3g0v0_Cancun_correctness:
  ∃s r.
    initial_state 1
      add_d3g0v0_Cancun_pre
      add_d3g0v0_Cancun_block
      (Memory <| offset := 0; size := 0 |>)
      add_d3g0v0_Cancun_transaction = SOME s ∧
    run s = SOME (Finished r) ∧
    update_beacon_block add_d3g0v0_Cancun_block $ (* TODO: proper block processing *)
    refund_fee
      add_d3g0v0_Cancun_transaction.from
      (* TODO: refund should be limited by gas used / 5 *)
      (add_d3g0v0_Cancun_block.baseFeePerGas * (r.refund + r.gasLeft))
      r.accounts
    = add_d3g0v0_Cancun_post
Proof
  rw[run_SOME_run_n, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`SOME _ = s`
  \\ `s <> NONE` by ( qunabbrev_tac`s` \\ cv_eval_match_tac``_``)
  \\ `∃n z t.
        run_with_fuel n (INL (), THE s) = SOME (Finished z, t, 0) ∧
        update_beacon_block add_d3g0v0_Cancun_block $
        refund_fee
          add_d3g0v0_Cancun_transaction.from
          (add_d3g0v0_Cancun_block.baseFeePerGas * (z.refund + z.gasLeft))
          z.accounts = add_d3g0v0_Cancun_post`
      suffices_by (
    strip_tac
    \\ Cases_on`s` \\ gs[]
    \\ drule run_with_fuel_to_zero
    \\ strip_tac
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gs[] )
  \\ qunabbrev_tac`s`
  \\ qmatch_asmsub_abbrev_tac`Memory m`
  \\ `m = memory_range 0 0` by (rw[Abbr`m`] \\ cv_eval_match_tac``_``)
  \\ fs[Abbr`m`]
  \\ qexists_tac`18`
  \\ cv_eval_run_with_fuel_tac
  \\ simp[] \\ EVAL_TAC
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM] \\ rw[] \\ gs[]
  \\ gs[account_state_component_equality, FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[] \\ gs[]
  \\ EVAL_TAC
QED

val test_name = el 5 test_names;
val test = get_test test_path test_name;

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
    "|>"
  ])]);

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

Theorem add_d4g0v0_Cancun_correctness:
  ∃s r.
    initial_state 1
      add_d4g0v0_Cancun_pre
      add_d4g0v0_Cancun_block
      (Memory <| offset := 0; size := 0 |>)
      add_d4g0v0_Cancun_transaction = SOME s ∧
    run s = SOME (Finished r) ∧
    update_beacon_block add_d4g0v0_Cancun_block $ (* TODO: proper block processing *)
    refund_fee
      add_d4g0v0_Cancun_transaction.from
      (* TODO: refund should be limited by gas used / 5 *)
      (add_d4g0v0_Cancun_block.baseFeePerGas * (r.refund + r.gasLeft))
      r.accounts
    = add_d4g0v0_Cancun_post
Proof
  rw[run_SOME_run_n, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`SOME _ = s`
  \\ `s <> NONE` by ( qunabbrev_tac`s` \\ cv_eval_match_tac``_``)
  \\ `∃n z t.
        run_with_fuel n (INL (), THE s) = SOME (Finished z, t, 0) ∧
        update_beacon_block add_d4g0v0_Cancun_block $
        refund_fee
          add_d4g0v0_Cancun_transaction.from
          (add_d4g0v0_Cancun_block.baseFeePerGas * (z.refund + z.gasLeft))
          z.accounts = add_d4g0v0_Cancun_post`
      suffices_by (
    strip_tac
    \\ Cases_on`s` \\ gs[]
    \\ drule run_with_fuel_to_zero
    \\ strip_tac
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gs[] )
  \\ qunabbrev_tac`s`
  \\ qmatch_asmsub_abbrev_tac`Memory m`
  \\ `m = memory_range 0 0` by (rw[Abbr`m`] \\ cv_eval_match_tac``_``)
  \\ fs[Abbr`m`]
  \\ qexists_tac`18`
  \\ cv_eval_run_with_fuel_tac
  \\ simp[] \\ EVAL_TAC
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM] \\ rw[] \\ gs[]
  \\ gs[account_state_component_equality, FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[] \\ gs[]
  \\ EVAL_TAC
QED

val _ = export_theory();
