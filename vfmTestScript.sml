open HolKernel boolLib bossLib Parse wordsLib
     whileTheory
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

Definition empty_accounts_def:
  empty_accounts (a: address) = empty_account_state
End

Theorem build_spt_empty_accounts[simp]:
  ∀n. build_spt empty_account_state n empty_accounts = LN
Proof
  Induct \\ rw[build_spt_def]
  \\ gs[empty_accounts_def]
QED

Theorem empty_accounts_cv_rep[cv_rep]:
  from_evm_accounts empty_accounts = Num 0
Proof
  rw[from_evm_accounts_def, from_sptree_sptree_spt_def]
QED

(* TODO:
initial_access_sets_def

val () = cv_auto_trans initial_state_def;
*)

(*
https://github.com/ethereum/tests
commit 08839f5 (taken from the develop branch)
BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json
*)

Definition add_d0g0v0_Cancun_block_def:
  add_d0g0v0_Cancun_block =
  <| number := 0x01
   ; baseFee := 0x0a
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

Triviality wf_state_add_d0g0v0_Cancun_pre:
  ∀c b r. wf_state (initial_state c add_d0g0v0_Cancun_pre b r add_d0g0v0_Cancun_transaction)
Proof
  ‘wf_accounts add_d0g0v0_Cancun_pre’ by (EVAL_TAC >> rw[])
  \\ rw[]
QED

Theorem add_d0g0v0_Cancun_pre_code:
  (add_d0g0v0_Cancun_pre add_d0g0v0_Cancun_transaction.to).code =
  hex_to_bytes "600060006000600060006004356110000162fffffff100"
Proof
  simp[add_d0g0v0_Cancun_pre_def, add_d0g0v0_Cancun_transaction_def,
       update_account_def]
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

Theorem lt_0_w2n_zero_bytes:
  (0 :num) >= w2n (word_of_bytes F (0w :256 word) [(0w :word8)])
Proof
  cv_eval_match_tac ``word_of_bytes _ _ _``
  \\ EVAL_TAC
QED

Theorem memory_expansion_cost_d0g0v0:
  memory_expansion_cost [] (PAD_RIGHT 0w (32 * word_size 0) []) + 2630 ≤ 80000000
Proof
  EVAL_TAC
QED

val () = mk_word_size 256;

Theorem set_byte_0ws:
  set_byte (0w:word256) 0w 0w e = 0w
Proof
  rw[set_byte_def]
  \\ EVAL_TAC
QED

Theorem assert_simps:
  assert T e s = (INL (), s) ∧
  assert F e s = (INR (Excepted e), s)
Proof
  rw[assert_def]
QED

val () = cv_auto_trans add_d0g0v0_Cancun_pre_def;
val () = add_d0g0v0_Cancun_post_def |>
  ONCE_REWRITE_RULE[GSYM update_storage_def] |>
  cv_auto_trans;
val () = cv_auto_trans add_d0g0v0_Cancun_transaction_def;
val () = cv_auto_trans add_d0g0v0_Cancun_block_def;

(*
Theorem add_d0g0v0_Cancun_correctness:
  ∃r. run (initial_state 1
    add_d0g0v0_Cancun_pre
    add_d0g0v0_Cancun_block
    (Memory <| offset := 0; size := 0 |>)
    add_d0g0v0_Cancun_transaction)
  = SOME (Finished r) ∧ r.accounts = add_d0g0v0_Cancun_post
Proof
  rw[run_def, Once OWHILE_THM, PULL_EXISTS]
  \\ cv_eval_match_tac ``step _``
  \\ cv_eval_match_tac ``(Memory _)``
  \\ cv_eval_match_tac ``(initial_state _ _ _ _ _)``
  initial_state_def
  cv_in
  ff"initial_state""cv"
  step_def

  \\ rw[step_def]
  \\ rw[Once bind_def]
  \\ eval_match_tac “get_current_context _”
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac ‘pair_CASE (_ _ ctx) body’
  \\ cv_eval_match_tac ``parse_opcode _`` \\ rw[]
  \\ rw[bind_def, ignore_bind_def, assert_def]
  \\ cv_eval_match_tac ``step_inst _``

  initial_state_def
  type_of``c.outputTo``
  TypeBase.fields_of``:memory_range`` |> map type_of
  type_of``Memory``
  initial_tx_params_def
  \\ cv_eval_match_tac ``step _``

  rpt (
    rw[run_def, Once OWHILE_THM, step_def]
    (* context *)
    \\rw[Once bind_def]
    \\ eval_match_tac “get_current_context _”
    \\rw[]

    \\qmatch_goalsub_abbrev_tac ‘pair_CASE (_ _ ctx) body’

    (* assert T *)
    \\rw[Once ignore_bind_def, Once bind_def, assert_def]
    \\cv_eval_match_tac “parse_opcode _”
    \\rw[]

    \\rw[Once ignore_bind_def, Once bind_def, consume_gas_def]
    \\rw[Once bind_def]
    \\eval_match_tac “get_current_context _”
    \\qunabbrev_tac ‘ctx’

    \\rw[Once ignore_bind_def, Once bind_def, assert_def]
    \\rw[Once ignore_bind_def, Once bind_def, set_current_context_def, return_def]
    \\rw[Once ignore_bind_def, Once bind_def, step_inst_def]
    \\eval_match_tac “get_current_context _”
    \\rw[]
    (* assert T *)
    \\rw[Once ignore_bind_def, Once bind_def, assert_def]
    \\rw[Once ignore_bind_def, Once bind_def, set_current_context_def, return_def]
    (* inc_pair *)
    \\rw[inc_pc_def]
    \\rw[Once bind_def]
    \\eval_match_tac “get_current_context _”
    \\ rw[]
    \\rw[Once ignore_bind_def, Once bind_def, set_current_context_def, return_def]

    \\unabbrev_all_tac
    \\rw[]
    )
  \\ rpt
     (
     rw[Once OWHILE_THM, step_def]
     \\qmatch_goalsub_abbrev_tac ‘pair_CASE (_ _ _) body’

     \\rw[Once bind_def]
     \\eval_match_tac “get_current_context _”
     \\rw[]
     (* assert T *)
     \\rw[Once ignore_bind_def, Once bind_def, assert_def]
     \\cv_eval_match_tac “parse_opcode _”
     \\rw[]
     (* consume gas *)
     \\rw[Once ignore_bind_def, Once bind_def, consume_gas_def]
     \\rw[Once bind_def]
     \\eval_match_tac “get_current_context _”
     \\rw[]
     (* assert T *)
     \\rw[Once ignore_bind_def, Once bind_def, assert_def]
     \\rw[set_current_context_def, return_def]

     (* step_inst *)
     \\rw[Once ignore_bind_def, Once bind_def]
     \\rw[step_inst_def]
     \\rw[binop_def, stack_op_def]
     \\rw[Once bind_def, step_inst_def]
     \\eval_match_tac “get_current_context _”
     \\rw[]
     (* assert T *)
     \\rw[Once ignore_bind_def, Once bind_def, assert_def]
     \\rw[set_current_context_def, return_def]

     \\rw[inc_pc_def, opcode_def]
     \\rw[Once bind_def]
     \\eval_match_tac “get_current_context _”
     \\rw[]
     \\rw[set_current_context_def, return_def]
     \\unabbrev_all_tac
     \\ rw[]
     )

  \\rw[set_byte_0ws]
  \\rw[Once OWHILE_THM, step_def]
  \\rw[Once bind_def]
  \\eval_match_tac “get_current_context _”
  \\rw[]
  (* assert T *)
  \\rw[Once ignore_bind_def, Once bind_def, assert_simps]
  (* parse opcode *)
  \\cv_eval_match_tac “parse_opcode _”
  \\rw[]

   (* CONSUME GAS *)
  \\rw[Once ignore_bind_def, Once bind_def, consume_gas_def]
  \\rw[Once bind_def]
  \\eval_match_tac “get_current_context _”
  \\rw[]
  (* assert T *)
  \\rw[Once ignore_bind_def, Once bind_def, assert_def]
  \\rw[set_current_context_def, return_def]

  \\rw[Once ignore_bind_def, Once bind_def]
  \\rw[step_inst_def]
  \\rw[Once bind_def]
  \\eval_match_tac “get_current_context _”
  \\rw[]
      (* assert T *)
  \\rw[Once ignore_bind_def, Once bind_def, assert_simps]
  \\rw[Once bind_def, access_address_def]
  (* return *)
  \\rw[return_def]
(* get accounts *)
  \\rw[Once bind_def, get_accounts_def]
  \\rw[return_def]
  \\rw[Once ignore_bind_def, Once bind_def, memory_expansion_cost_def]
  \\rw[memory_cost_def]
  \\ ‘word_size 0 = 0’ by rw[word_size_def]
  \\rw[]
  \\rw[bitstringTheory.length_pad_right]
      (* consume gas *)
  \\rw[Once ignore_bind_def, Once bind_def, consume_gas_def]
  \\eval_match_tac “get_current_context _”
  \\rw[]
  \\rw[Once bind_def, assert_simps]
  \\rw[set_current_context_def, return_def]
      (* assert T *)
  \\rw[Once ignore_bind_def, Once bind_def, assert_simps]
  \\rw[Once ignore_bind_def, Once bind_def]
  \\rw[Once bind_def]
  \\eval_match_tac “get_current_context _”
  \\rw[]

  \\ cheat
QED
Globals.max_print_depth := ~1;
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
