Theory vfmBuffer
Ancestors
  arithmetic list rich_list words vfmTypes
Libs
  cv_transLib intLib wordsLib

(* A byte buffer with constant-time length and random access, used for
   memory and call data.  Byte i of a buffer is digit i of contents in base
   256; bytes at or past len are zero. *)

Datatype:
  buffer = <| len : num; contents : num |>
End

(* The first n bytes of x, least significant first, followed by acc.
   Splitting in halves keeps the cost proportional to n log n. *)
Definition bytes_of_num_def:
  bytes_of_num n (x:num) (acc:byte list) =
  if n = 0 then acc else
  if n ≤ 32 then n2w (x MOD 256) :: bytes_of_num (n - 1) (x DIV 256) acc
  else let h = n DIV 2 in
    bytes_of_num h (x MOD 2 ** (8 * h))
      (bytes_of_num (n - h) (x DIV 2 ** (8 * h)) acc)
End

(* The number whose base-256 digits, least significant first, are the first
   n bytes of bs (missing bytes count as zero). *)
Definition num_of_bytes_def:
  num_of_bytes n (bs:byte list) =
  if n = 0 then 0n else
  if n ≤ 32 then
    (case bs of [] => 0 | b::rest => w2n b + 256 * num_of_bytes (n - 1) rest)
  else let h = n DIV 2 in
    num_of_bytes h bs + 2 ** (8 * h) * num_of_bytes (n - h) (DROP h bs)
End

Definition empty_buffer_def:
  empty_buffer = <| len := 0; contents := 0 |>
End

Definition buffer_length_def:
  buffer_length b = b.len
End

Definition buffer_of_list_def:
  buffer_of_list bs =
  <| len := LENGTH bs; contents := num_of_bytes (LENGTH bs) bs |>
End

(* the size bytes starting at offset, zero past the end *)
Definition buffer_read_def:
  buffer_read offset size b =
  bytes_of_num size ((b.contents DIV 2 ** (8 * offset)) MOD 2 ** (8 * size)) []
End

Definition buffer_to_list_def:
  buffer_to_list b = buffer_read 0 b.len b
End

(* the size bytes starting at offset, as a buffer of length size *)
Definition buffer_sub_def:
  buffer_sub offset size b =
  <| len := size;
     contents := (b.contents DIV 2 ** (8 * offset)) MOD 2 ** (8 * size) |>
End

(* n zero bytes added at the end *)
Definition buffer_extend_def:
  buffer_extend n b = b with len := b.len + n
End

(* bytes written over the buffer starting at offset *)
Definition buffer_write_def:
  buffer_write offset bytes b =
  let k = LENGTH bytes in
  let lo = b.contents MOD 2 ** (8 * offset) in
  let hi = b.contents DIV 2 ** (8 * (offset + k)) in
  <| len := MAX b.len (offset + k);
     contents := lo + 2 ** (8 * offset) * num_of_bytes k bytes
                 + 2 ** (8 * (offset + k)) * hi |>
End

val () = cv_auto_trans_rec bytes_of_num_def
  (WF_REL_TAC ‘measure (cv$c2n o FST)’
   \\ rpt strip_tac \\ Cases_on ‘cv_n’ \\ gvs[cvTheory.c2b_def]
   \\ rpt (pop_assum mp_tac) \\ rw[]
   \\ intLib.ARITH_TAC);

val () = cv_auto_trans_rec num_of_bytes_def
  (WF_REL_TAC ‘measure (cv$c2n o FST)’
   \\ rpt strip_tac \\ Cases_on ‘cv_n’ \\ gvs[cvTheory.c2b_def]
   \\ rpt (pop_assum mp_tac) \\ rw[]
   \\ intLib.ARITH_TAC);
val () = cv_auto_trans empty_buffer_def;
val () = cv_auto_trans buffer_length_def;
val () = cv_auto_trans buffer_of_list_def;
val () = cv_auto_trans buffer_read_def;
val () = cv_auto_trans buffer_to_list_def;
val () = cv_auto_trans buffer_sub_def;
val () = cv_auto_trans buffer_extend_def;
val () = cv_auto_trans buffer_write_def;
