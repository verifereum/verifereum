open HolKernel wordsTheory;
val _ = new_theory "vfmTypes";

Type address = “:160 word”
Type bytes32 = “:256 word”
Type byte = “:word8”

val _ = export_theory();
