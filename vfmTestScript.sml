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

val _ = export_theory();
