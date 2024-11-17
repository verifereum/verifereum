open HolKernel wordsTheory finite_mapTheory ParseExtras keccakTheory;

val _ = new_theory "vfmTypes";

val _ = tight_equality();

(* TODO: move? *)
Definition Keccak_256_bytes_def:
  Keccak_256_bytes (bs:word8 list) : word8 list =
    MAP bools_to_word $ chunks 8 $
    Keccak_256 $
    MAP ((=) 1) $ FLAT $
    MAP (PAD_RIGHT 0 8 o word_to_bin_list) bs
End

Type address = “:160 word”
Type bytes32 = “:256 word”
Type byte = “:word8”
Datatype:
  event =
  <| logger : address
   ; topics : bytes32 list
   ; data : byte list
   |>
End

val _ = export_theory();
