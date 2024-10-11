open HolKernel boolLib bossLib Parse wordsLib dep_rewrite
     arithmeticTheory whileTheory
     vfmTypesTheory vfmExecutionTheory
     vfmStateTheory vfmContextTheory
     vfmOperationTheory vfmComputeTheory
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

Definition add_d0g0v0_Cancun_block_def:
  add_d0g0v0_Cancun_block =
  <| number := 0x01
   ; baseFeePerGas := 0x0a
   ; timeStamp := 0x03e8
   ; coinBase := n2w 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba
   ; gasLimit := 0x05f5e100
   ; prevRandao := n2w 0x00 (* not sure - using the difficulty *)
  |>
End

Definition add_d0g0v0_Cancun_transaction_def:
  add_d0g0v0_Cancun_transaction =
  <| from := n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b
   ; to   := n2w 0xcccccccccccccccccccccccccccccccccccccccc
   ; data := hex_to_bytes $ CONCAT [
               "693c61390000000000000000000000000000";
               "000000000000000000000000000000000000" ]
   ; nonce := 0x00
   ; value := 0x01
   ; gasPrice := 0x0a
   ; gasLimit := 0x04c4b400
   ; accessList := []
   |>
End

Definition add_d0g0v0_Cancun_pre_def:
  add_d0g0v0_Cancun_pre =
  update_account (
  update_account (
  update_account (
  update_account (
  update_account (
  update_account (
  update_account empty_accounts
    (n2w 0x0000000000000000000000000000000000001000)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["7ffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffffffffffffffff7fffffffffff"
                 ;"fffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001001)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60047fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001002)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60017fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001003)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes "600060000160005500"
     |>
  )
    (n2w 0x0000000000000000000000000000000000001004)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                  ["7fffffffffffffffffffffffffffffffffffffff"
                  ;"ffffffffffffffffffffffffff60010160005500"]
     |>
  )
    (n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := []
     |>
  )
    (n2w 0xcccccccccccccccccccccccccccccccccccccccc)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes "600060006000600060006004356110000162fffffff100"
     |>
End

Definition add_d0g0v0_Cancun_post_def:
  add_d0g0v0_Cancun_post =
  update_account (
  update_account (
  update_account (
  update_account (
  update_account (
  update_account (
  update_account empty_accounts
    (n2w 0x0000000000000000000000000000000000001000)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := (n2w 0x00 =+ n2w 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe) empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["7ffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffffffffffffffff7fffffffffff"
                 ;"fffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001001)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60047fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001002)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60017fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001003)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes "600060000160005500"
     |>
  )
    (n2w 0x0000000000000000000000000000000000001004)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                  ["7fffffffffffffffffffffffffffffffffffffff"
                  ;"ffffffffffffffffffffffffff60010160005500"]
     |>
  )
    (n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b)
    <| nonce := 0x01
     ; balance := 0x0ba1a9ce0b9aa781
     ; storage := empty_storage
     ; code := []
     |>
  )
    (n2w 0xcccccccccccccccccccccccccccccccccccccccc)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9cf
     ; storage := empty_storage
     ; code := hex_to_bytes "600060006000600060006004356110000162fffffff100"
     |>
End

Theorem add_d0g0v0_Cancun_pre_code:
  (add_d0g0v0_Cancun_pre add_d0g0v0_Cancun_transaction.to).code =
  hex_to_bytes "600060006000600060006004356110000162fffffff100"
Proof
  simp[add_d0g0v0_Cancun_pre_def, add_d0g0v0_Cancun_transaction_def,
       update_account_def]
QED

val () = cv_auto_trans add_d0g0v0_Cancun_pre_def;
val () = add_d0g0v0_Cancun_post_def |>
  ONCE_REWRITE_RULE[GSYM update_storage_def] |>
  cv_auto_trans;
val () = cv_auto_trans add_d0g0v0_Cancun_transaction_def;
val () = cv_auto_trans add_d0g0v0_Cancun_block_def;

(*

cv_eval ``
let s =
(run_n 18 (THE (initial_state 1
    add_d0g0v0_Cancun_pre
    add_d0g0v0_Cancun_block
    (Memory <| offset := 0; size := 0 |>)
    add_d0g0v0_Cancun_transaction))) in
let c = EL 0 (SND s).contexts in
  (c.callParams.gasLimit, c.gasUsed, c.gasRefund, c.stack,
  c.callParams.outputTo, c.returnData)
``

val cappedGas = 16777215
val stipend = 0
cappedGas + stipend
val callerGasUsed = 16779845
val accessCost = 2600
val expansionCost = 0
val callCost = callerGasUsed - 30
val true = callCost - cappedGas = accessCost
val executionCost = 22112
val calleeGasLeft = cappedGas - executionCost
val newGasUsed = callerGasUsed - calleeGasLeft

val senderAfterMine = 838137707291124173
val senderAfterCorrect = 0x0ba1a9ce0b9aa781
val discrepancy = senderAfterCorrect - senderAfterMine
val gasLimit = 79978808
gasLimit - newGasUsed
discrepancy

cv_eval ``
  (EL 0 (SND (run_n 11 (initial_state 1
    add_d0g0v0_Cancun_pre
    add_d0g0v0_Cancun_block
    (Memory <| offset := 0; size := 0 |>)
    add_d0g0v0_Cancun_transaction))).contexts).pc
``

initial_context_def

val callee_code = cv_eval ``
  (HD (SND (run_n 12 (initial_state 1
    add_d0g0v0_Cancun_pre
    add_d0g0v0_Cancun_block
    (Memory <| offset := 0; size := 0 |>)
    add_d0g0v0_Cancun_transaction))).contexts).callParams.code
`` |> concl |> rand |> rhs

cv_eval ``parse_opcode (DROP 0 ^callee_code)``
Push32 -1
Push32 -1
Add
Push1 0
SStore
Stop

TypeBase.fields_of``:transaction_state`` |> map fst
TypeBase.fields_of``:context`` |> map fst
TypeBase.fields_of``:call_parameters`` |> map fst

cv_eval ``parse_opcode (DROP 21 ^(rhs(concl add_d0g0v0_Cancun_pre_code)))``
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
Stop
*)

open cv_typeTheory cvTheory

Theorem add_d0g0v0_Cancun_correctness:
  ∃s r.
    initial_state 1
      add_d0g0v0_Cancun_pre
      add_d0g0v0_Cancun_block
      (Memory <| offset := 0; size := 0 |>)
      add_d0g0v0_Cancun_transaction = SOME s ∧
    run s = SOME (Finished r) ∧
    refund_fee
      add_d0g0v0_Cancun_transaction.from
      (* TODO: refund should be limited by gas used / 5 *)
      (add_d0g0v0_Cancun_block.baseFeePerGas * (r.refund + r.gasLeft))
      r.accounts
    = add_d0g0v0_Cancun_post
Proof
  rw[run_SOME_run_n, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`SOME _ = s`
  \\ `s <> NONE`
   by ( qunabbrev_tac`s` \\ cv_eval_match_tac``_``)
  \\ `∃n z t.
        run_with_fuel n (INL (), THE s) = SOME (Finished z, t, 0) ∧
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
  \\ (fn goal as (_, gt) =>
    let
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
    end goal)
  \\ simp[] \\ EVAL_TAC
  \\ rw[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ Cases_on`x = 0x0000000000000000000000000000000000001000w`
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ Cases_on`x = 0x0000000000000000000000000000000000001001w`
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ Cases_on`x = 0x0000000000000000000000000000000000001002w`
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ Cases_on`x = 0x0000000000000000000000000000000000001003w`
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ Cases_on`x = 0x0000000000000000000000000000000000001004w`
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ gs[]
  \\ Cases_on`x = 0xccccccccccccccccccccccccccccccccccccccccw`
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ gs[]
  \\ rw[]
  >- gs[account_state_component_equality, FUN_EQ_THM]
  \\ EVAL_TAC
QED

(*
val ts_tm = raw_th2 |> concl |> rhs |> rand |> rand

ts_tm |>
REWRITE_CONV[
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
          |> concl |> rhs

val to_sptree_spt_cs = computeLib.bool_compset();
val () = computeLib.add_thms [
  to_sptree_spt_def,
  cv_has_shape_def,
  cv_snd_def,
  cv_fst_def
] to_sptree_spt_cs;

val spt_tm = raw_th2 |> concl |>
  find_term (can (match_term ``to_sptree_spt _ _``))

rawterm_pp (fn () => (concl (EVAL spt_tm))) ()
val probtm = rhs(concl(EVAL spt_tm))
el 3 (snd (strip_comb probtm))
term_size probtm

computeLib.CBV_CONV to_sptree_spt_cs spt_tm
spt_tm |> term_size
PolyML.Exception.traceException((fn () =>
  term_to_string (concl (EVAL spt_tm))),(fn (ss,e) => String.concat(ss)))
(term_to_string (concl (EVAL spt_tm)); NONE)
handle e => PolyML.Exception.exceptionLocation e
(if aconv (concl (EVAL spt_tm)) T then SOME {endLine=0, endPosition=0, file="done", startLine=0,
startPosition=0} else NONE) handle e => PolyML.Exception.exceptionLocation e

Int.maxInt
*)

(*
Definition CrashingTransaction_transaction_def:
  CrashingTransaction_transaction =
  <| from     := n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b
   ; to       := n2w 0x0
   ; data     := hex_to_bytes $ CONCAT
                 ["60606040525b5b61c3505a1115602c57604051603480"
                 ;"6039833901809050604051809103906000f050600656"
                 ;"5b5b600a80606d6000396000f360606040525b3373ff"
                 ;"ffffffffffffffffffffffffffffffffffffff16ff5b"
                 ;"600a80602a6000396000f360606040526008565b0060"
                 ;"606040526008565b00"]
   ; nonce    := 0x0cc6
   ; value    := 0x01
   ; gasLimit := 0x47127a
   ; gasPrice := 0x0b
   ; accessList := []
   |>
End
secretKey = 0x45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8

Definition CrashingTransaction_pre_def:
  CrashingTransaction_pre accounts ⇔
  let account = accounts (n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b) in
    account.balance = 0x0de0b6b3a7640000 ∧
    account.code = [] ∧
    account.nonce = 0x0cc6 ∧
    account.storage = K 0w
End

(*
Definition CrashingTransaction_post_def:
  CrashingTransaction_post r ⇔
    state hash = n2w 0x7f2928f3c2a99e47eedce1880f49dbf3c44f9d304ec80bb7a14d755fae19a518
    logs hash = n2w 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347

                    "txbytes" : "0xf8c6820cc60b8347127a8001b87760606040525b5b61c3505a1115602c576040516034806039833901809050604051809103906000f0506006565b5b600a80606d6000396000f360606040525b3373ffffffffffffffffffffffffffffffffffffffff16ff5b600a80602a6000396000f360606040526008565b0060606040526008565b001ba0e3ff099a5b59f34c2e88fd6a42e44bf6ae186ebd06fa62aa18044da6a6d98df3a03efe897c69df0d45e18dd61580de2b700952cc9bc794fe05d0c6bf5e7f63d1d1"
*)
*)

val _ = export_theory();
