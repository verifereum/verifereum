open HolKernel wordsTheory ParseExtras;

val _ = new_theory "vfmTypes";

val _ = tight_equality();

Type address = “:160 word”
Type bytes32 = “:256 word”
Type byte = “:word8”

val _ = export_theory();
