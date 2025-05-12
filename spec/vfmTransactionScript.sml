open HolKernel boolLib bossLib Parse
     cv_transLib cv_typeLib wordsLib
     wordsTheory finite_setTheory
     vfmConstantsTheory vfmTypesTheory
     recursiveLengthPrefixTheory;

val _ = new_theory "vfmTransaction";

Datatype:
  access_list_entry =
  <| account : address
   ; keys    : bytes32 list
   |>
End

val from_to_access_list_entry = from_to_thm_for “:access_list_entry”;

Datatype:
  transaction =
  <| from       : address
   ; to         : address option
   ; data       : byte list
   ; nonce      : num
   ; value      : num
   ; gasLimit   : num
   ; gasPrice   : num
   ; accessList : access_list_entry list
   ; blobVersionedHashes : bytes32 list
   ; maxFeePerBlobGas : num option
   ; maxFeePerGas : num option
   |>
End

val from_to_transaction = from_to_thm_for “:transaction”;

Definition effective_gas_price_def:
  effective_gas_price baseFee maxFee maxPrioFee =
  let prioFee = MIN maxPrioFee (maxFee - baseFee) in
    baseFee + prioFee
End

val () = cv_auto_trans effective_gas_price_def;

Definition total_blob_gas_def:
  total_blob_gas tx = gas_per_blob * LENGTH tx.blobVersionedHashes
End

val () = cv_auto_trans total_blob_gas_def;

Definition max_total_cost_def:
  max_total_cost tx =
  tx.gasLimit * (case tx.maxFeePerGas of SOME x => x | NONE => tx.gasPrice)
  + (case tx.maxFeePerBlobGas of SOME x => x * total_blob_gas tx | _ => 0)
  + tx.value
End

val () = cv_auto_trans max_total_cost_def;

Definition rlp_event_def:
  rlp_event ev = RLPL [
    RLPB $ word_to_bytes ev.logger T;
    RLPL $ MAP (λt. RLPB (word_to_bytes ((w2w t):word32) T))
           ev.topics;
    RLPB ev.data
  ]
End

val () = cv_auto_trans rlp_event_def;

val _ = export_theory();
