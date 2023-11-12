open HolKernel boolLib bossLib Parse
     finite_mapTheory
     vfmTypesTheory vfmOperationTheory;

val _ = new_theory "vfmContext";

Datatype:
  callvars =
  <| origin     : address
   ; caller     : address
   ; callee     : address
   ; value      : num
   ; code       : byte list
   ; calldata   : byte list
   ; gasPrice   : num
   ; baseFee    : num
   |>
End

Datatype:
  context =
  <| stack      : bytes32 list
   ; memory     : bytes32 list
   ; pc         : num
   ; storage    : bytes32 |-> bytes32
   ; returndata : byte list
   ; gasUsed    : num
   ; gasLeft    : num
   ; accAddress : address set
   ; accStorage : bytes32 set
   |>
End

val _ = export_theory();
