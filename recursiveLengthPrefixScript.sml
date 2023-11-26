open HolKernel boolLib bossLib Parse
     wordsLib wordsTheory;

val _ = new_theory "recursiveLengthPrefix";

Definition rlp_bytes_def:
  rlp_bytes (bytes : word8 list) =
  if LENGTH bytes = 1 ∧ w2n (HD bytes) < 128 then bytes
  else if LENGTH bytes < 56 then n2w (128 + LENGTH bytes) :: bytes
  else
    let lengthBytes = MAP n2w $ REVERSE $ n2l 256 $ LENGTH bytes
  in
    [n2w (183 + LENGTH lengthBytes)] ++ lengthBytes ++ bytes
End

Definition rlp_list_def:
  rlp_list (payload : word8 list) =
  if LENGTH payload < 56 then n2w (192 + LENGTH payload) :: payload
  else
    let lengthBytes = MAP n2w $ REVERSE $ n2l 256 $ LENGTH payload
  in
    [n2w (248 + LENGTH lengthBytes)] ++ lengthBytes ++ payload
End

val _ = export_theory();
