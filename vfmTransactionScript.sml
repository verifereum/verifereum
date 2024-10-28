open HolKernel boolLib bossLib Parse
     wordsTheory finite_setTheory
     vfmTypesTheory;

val _ = new_theory "vfmTransaction";

Datatype:
  access_list_entry =
  <| account : address
   ; keys    : bytes32 fset
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
   |>
End

val _ = export_theory();
