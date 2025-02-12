open HolKernel boolLib bossLib Parse
     wordsTheory finite_setTheory
     vfmTypesTheory;

val _ = new_theory "vfmTransaction";

Datatype:
  access_list_entry =
  <| account : address
   ; keys    : bytes32 list
   |>
End

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
   ; blobGasPrice : num
   |>
End

Definition effective_gas_price_def:
  effective_gas_price baseFee maxFee maxPrioFee =
  let prioFee = MIN maxPrioFee (maxFee - baseFee) in
    baseFee + prioFee
End

val _ = export_theory();
