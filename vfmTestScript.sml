open HolKernel boolLib bossLib Parse wordsLib
     whileTheory
     vfmTypesTheory vfmExecutionTheory
     vfmStateTheory vfmContextTheory
     vfmOperationTheory
     cv_transLib cv_stdTheory cv_computeLib;

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

(* BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json *)

Definition add_d0g0v0_Shanghai_transaction_def:
  add_d0g0v0_Shanghai_transaction =
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

Definition add_d0g0v0_Shanghai_pre_def:
  add_d0g0v0_Shanghai_pre a =
  if a = n2w 0x0000000000000000000000000000000000001000 then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["7ffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffffffffffffffff7fffffffffff"
                 ;"fffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffff0160005500"]
     |>
  else if a = n2w 0x0000000000000000000000000000000000001001 then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60047fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  else if a = n2w 0x0000000000000000000000000000000000001002 then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60017fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  else if a = n2w 0x0000000000000000000000000000000000001003 then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes "600060000160005500"
     |>
  else if a = n2w 0x0000000000000000000000000000000000001004 then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                  ["7fffffffffffffffffffffffffffffffffffffff"
                  ;"ffffffffffffffffffffffffff60010160005500"]
     |>
  else if a = n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := []
     |>
  else if a = n2w 0xcccccccccccccccccccccccccccccccccccccccc then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes "600060006000600060006004356110000162fffffff100"
     |>
  else empty_account_state
End

Definition add_d0g0v0_Shanghai_post_def:
  add_d0g0v0_Shanghai_post a =
  if a = n2w 0x0000000000000000000000000000000000001000 then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := (n2w 0x00 =+ n2w 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe) empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["7ffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffffffffffffffff7fffffffffff"
                 ;"fffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffff0160005500"]
     |>
  else if a = n2w 0x0000000000000000000000000000000000001001 then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60047fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  else if a = n2w 0x0000000000000000000000000000000000001002 then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60017fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  else if a = n2w 0x0000000000000000000000000000000000001003 then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes "600060000160005500"
     |>
  else if a = n2w 0x0000000000000000000000000000000000001004 then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                  ["7fffffffffffffffffffffffffffffffffffffff"
                  ;"ffffffffffffffffffffffffff60010160005500"]
     |>
  else if a = n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b then
    <| nonce := 0x01
     ; balance := 0x0ba1a9ce0b9aa781
     ; storage := empty_storage
     ; code := []
     |>
  else if a = n2w 0xcccccccccccccccccccccccccccccccccccccccc then
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9cf
     ; storage := empty_storage
     ; code := hex_to_bytes "600060006000600060006004356110000162fffffff100"
     |>
  else empty_account_state
End


Triviality wf_state_add_d0g0v0_Shanghai_pre:
  ∀c b r. wf_state (initial_state c add_d0g0v0_Shanghai_pre b r add_d0g0v0_Shanghai_transaction)
Proof
  ‘wf_accounts (add_d0g0v0_Shanghai_pre :160 word -> account_state)’
    by (EVAL_TAC >> rw[])
  \\ rw[]
QED

Theorem add_d0g0v0_Shanghai_pre_code:
  (add_d0g0v0_Shanghai_pre add_d0g0v0_Shanghai_transaction.to).code =
  hex_to_bytes "600060006000600060006004356110000162fffffff100"
Proof
  simp[add_d0g0v0_Shanghai_pre_def, add_d0g0v0_Shanghai_transaction_def]
QED

fun cv_eval_match_tac pat =
  goal_term (fn tm =>
               let
                 val t = find_term (can (match_term pat)) tm
               in rewrite_tac [cv_eval t] end);

Theorem add_d0g0v0_Shanghai_correctness:
  ∀c b rd.
    ∃r. run (initial_state c add_d0g0v0_Shanghai_pre b rd add_d0g0v0_Shanghai_transaction)
    = SOME (Finished r) ∧ r.accounts = add_d0g0v0_Shanghai_post
Proof
  rw[run_def, PULL_EXISTS]
  \\ rw[Once OWHILE_THM]
  \\ simp[step_def]
  \\ simp[Once initial_state_def]
  \\ simp[Once bind_def, get_current_context_def, Once return_def]
  \\ simp[add_d0g0v0_Shanghai_pre_code]
  \\ rw [cv_eval “hex_to_bytes "600060006000600060006004356110000162fffffff100"”]
  \\ rw[cv_eval “ parse_opcode  [96w; 0w; 96w; 0w; 96w; 0w; 96w; 0w; 96w; 0w; 96w; 4w; 53w;
                  97w; 16w; 0w; 1w; 98w; 255w; 255w; 255w; 241w; 0w]”]
  \\ rw[Once ignore_bind_def, Once bind_def, assert_def]
  \\ rw[Once ignore_bind_def, Once bind_def, consume_gas_def]
  \\ rw[Once bind_def, get_current_context_def, return_def]
  \\ rw[Once ignore_bind_def, bind_def, assert_def, set_current_context_def, return_def,  add_d0g0v0_Shanghai_transaction_def]

  (* step instr *)
  \\ rw[Once ignore_bind_def, Once bind_def, step_inst_def]
  \\ rw[Once bind_def, get_current_context_def]
  \\ rw[return_def]
  \\ rw[Once ignore_bind_def, Once bind_def, assert_def]
  \\ rw[set_current_context_def, return_def]
  (* inc pc *)
  \\ rw[inc_pc_def, Once bind_def, get_current_context_def, return_def, set_current_context_def]

  (* opcode 2 *)
  \\ rw[Once OWHILE_THM]
  \\ rw[step_def]
  \\ rw[Once bind_def, get_current_context_def, return_def]
  \\ fs[opcode_def]
  \\ rw[Once ignore_bind_def, Once bind_def, assert_def]
  \\ rw[opcode_def]
  \\ rw[cv_eval “parse_opcode
                     [96w; 0w; 96w; 0w; 96w; 0w; 96w; 0w; 96w; 4w; 53w; 97w;
                      16w; 0w; 1w; 98w; 255w; 255w; 255w; 241w; 0w]”]
  \\ rw[Once ignore_bind_def, Once bind_def, consume_gas_def]
  \\ rw[Once bind_def, get_current_context_def]
  \\ rw[Once return_def]
  \\ rw[Once ignore_bind_def, Once bind_def, assert_def]
  \\ rw[set_current_context_def, Once return_def]

  (* copy block till next from above *)
  \\ rw[Once ignore_bind_def, Once bind_def, step_inst_def]
  \\ rw[Once bind_def, get_current_context_def]
  \\ rw[return_def]
  \\ rw[Once ignore_bind_def, Once bind_def, assert_def]
  \\ rw[set_current_context_def, return_def]
  \\ rw[inc_pc_def, Once bind_def, get_current_context_def, return_def, set_current_context_def]

  (* opcode 3 *)
  \\ rw[Once OWHILE_THM]
  \\ rw[step_def]
  \\ rw[Once bind_def, get_current_context_def, return_def]
  \\ fs[opcode_def]
  \\ rw[Once ignore_bind_def, Once bind_def, assert_def]
  \\ rw[opcode_def]
  \\ cv_eval_match_tac ``parse_opcode _``
  \\ rw[Once ignore_bind_def, Once bind_def, consume_gas_def]
  \\ rw[Once bind_def, get_current_context_def]
  \\ rw[Once return_def]
  \\ rw[Once ignore_bind_def, Once bind_def, assert_def]
  \\ rw[set_current_context_def, Once return_def]

  (* copy block till next from above *)
  \\ rw[Once ignore_bind_def, Once bind_def, step_inst_def]
  \\ rw[Once bind_def, get_current_context_def]
  \\ rw[return_def]
  \\ rw[Once ignore_bind_def, Once bind_def, assert_def]
  \\ rw[set_current_context_def, return_def]
  \\ rw[inc_pc_def, Once bind_def, get_current_context_def, return_def, set_current_context_def]

  (* here *)
  \\ cheat
QED

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
