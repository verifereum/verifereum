open HolKernel wordsTheory finite_mapTheory ParseExtras;

val _ = new_theory "vfmTypes";

val _ = tight_equality();

Type address = “:160 word”
Type bytes32 = “:256 word”
Type byte = “:word8”
Type finite_domain = “:α |-> unit”
Datatype:
  event =
  <| logger : address
   ; topics : bytes32 list
   ; data : byte list
   |>
End

val _ = export_theory();
