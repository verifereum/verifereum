open HolKernel boolLib bossLib Parse
     vfmTypesTheory vfmExecutionTheory;

val _ = new_theory "vfmTest";

(* TODO: move/replace *)
Definition hex_to_bytes_def:
    hex_to_bytes [] = [] : byte list
  ∧ hex_to_bytes (c1::c2::rest) =
      n2w (16 * UNHEX c1 + UNHEX c2)
      :: hex_to_bytes rest
End

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
