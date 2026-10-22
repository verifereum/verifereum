Theory vfmBuffer
Ancestors
  arithmetic list rich_list words sptree vfmTypes
Libs
  cv_transLib intLib wordsLib

(* A byte buffer with constant-time length and logarithmic-time access, used
   for memory and call data.  Bytes are grouped into 32-byte words: word i
   holds bytes 32 * i to 32 * i + 31, byte 32 * i + j being digit j of the word
   in base 256.  Only nonzero words are stored, and nonzero counts them, so
   that copying a range can visit whichever is fewer: the stored words or the
   words in the range.  Bytes at or past len are zero. *)

Datatype:
  buffer = <| len : num; words : num num_map; nonzero : num |>
End

(* the first n bytes of x, least significant first, followed by acc; x is
   split into 7-byte pieces first so that the byte loop runs on small
   numbers *)
Definition small_bytes_of_num_def:
  small_bytes_of_num (n:num) (x:num) (acc:byte list) =
  if n = 0 then acc
  else n2w (x MOD 256) :: small_bytes_of_num (n - 1) (x DIV 256) acc
Termination
  WF_REL_TAC ‘measure FST’
End

Definition bytes_of_num_def:
  bytes_of_num (n:num) (x:num) (acc:byte list) =
  if n ≤ 7 then small_bytes_of_num n x acc
  else small_bytes_of_num 7 (x MOD 2 ** 56)
         (bytes_of_num (n - 7) (x DIV 2 ** 56) acc)
Termination
  WF_REL_TAC ‘measure FST’
End

(* the number whose base-256 digits, least significant first, are bs *)
Definition num_of_bytes_def:
  num_of_bytes [] = 0n ∧
  num_of_bytes ((b:byte)::bs) = w2n b + 256 * num_of_bytes bs
End

Definition word_at_def:
  word_at ws (i:num) = case lookup i ws of NONE => 0n | SOME w => w
End

(* set word i to x, keeping the count of nonzero words *)
Definition set_word_def:
  set_word ws nz i x =
  let old = word_at ws i in
  if x = 0 then
    (if old = 0 then (ws, nz) else (delete i ws, nz - 1n))
  else (insert i x ws, if old = 0 then nz + 1 else nz)
End

(* n bytes starting at byte offset, followed by acc *)
Definition read_bytes_def:
  read_bytes ws (offset:num) (n:num) (acc:byte list) =
  if n = 0 then acc else
  let j = offset MOD 32 in
  let c = MIN n (32 - j) in
  bytes_of_num c (word_at ws (offset DIV 32) DIV 256 ** j)
    (read_bytes ws (offset + c) (n - c) acc)
Termination
  WF_REL_TAC ‘measure (FST o SND o SND)’ \\ rw[MIN_DEF]
  \\ irule (DECIDE “a < 32n ⇒ 0 < 32 − a”) \\ simp[]
End

(* write the first n bytes of bs starting at byte offset *)
Definition write_bytes_def:
  write_bytes ws (nz:num) (offset:num) (n:num) (bs:byte list) =
  if n = 0 then (ws, nz) else
  let i = offset DIV 32 in
  let j = offset MOD 32 in
  let c = MIN n (32 - j) in
  let old = word_at ws i in
  let new = old MOD 256 ** j + 256 ** j * num_of_bytes (TAKE c bs)
            + 256 ** (j + c) * (old DIV 256 ** (j + c)) in
  let p = set_word ws nz i new in
    write_bytes (FST p) (SND p) (offset + c) (n - c) (DROP c bs)
Termination
  WF_REL_TAC ‘measure (FST o SND o SND o SND)’ \\ rw[MIN_DEF]
  \\ irule (DECIDE “a < 32n ⇒ 0 < 32 − a”) \\ simp[]
End

(* the number formed by the c bytes (c ≤ 32) starting at byte offset *)
Definition read_word_def:
  read_word ws (offset:num) (c:num) =
  let i = offset DIV 32 in
  let j = offset MOD 32 in
  let k = MIN c (32 - j) in
  let lo = (word_at ws i DIV 256 ** j) MOD 256 ** k in
  if k < c then lo + 256 ** k * (word_at ws (i + 1) MOD 256 ** (c - k))
  else lo
End

(* words of the n bytes starting at offset, looked up one output word at a
   time; q is the index of the next output word *)
Definition sub_by_lookup_def:
  sub_by_lookup ws (offset:num) (n:num) (q:num) acc (nz:num) =
  if n = 0 then (acc, nz) else
  let c = MIN n 32 in
  let v = read_word ws offset c in
  sub_by_lookup ws (offset + c) (n - c) (q + 1)
    (if v = 0 then acc else insert q v acc) (if v = 0 then nz else nz + 1n)
Termination
  qexists_tac ‘measure (λ(ws,offset,n,rest). n)’ \\ rw[MIN_DEF]
End

(* add the c bytes (c ≤ 32) of v at byte pos of a buffer being built from
   disjoint pieces *)
Definition add_bytes_def:
  add_bytes ws (nz:num) (pos:num) (c:num) (v:num) =
  let i = pos DIV 32 in
  let j = pos MOD 32 in
  let k = MIN c (32 - j) in
  let p = set_word ws nz i (word_at ws i + (v MOD 256 ** k) * 256 ** j) in
  if k < c then
    set_word (FST p) (SND p) (i + 1) (word_at (FST p) (i + 1) + v DIV 256 ** k)
  else p
End

(* words of the n bytes starting at offset, built from the stored words *)
Definition sub_by_entries_def:
  sub_by_entries offset n [] ws nz = (ws, nz) ∧
  sub_by_entries offset n ((i, w)::rest) ws nz =
  let lo = MAX (32 * i) offset in
  let hi = MIN (32 * i + 32) (offset + n) in
  if hi ≤ lo then sub_by_entries offset n rest ws nz else
  let p = add_bytes ws nz (lo - offset) (hi - lo)
            ((w DIV 256 ** (lo - 32 * i)) MOD 256 ** (hi - lo)) in
  sub_by_entries offset n rest (FST p) (SND p)
End

Definition empty_buffer_def:
  empty_buffer = <| len := 0; words := LN; nonzero := 0 |>
End

Definition buffer_length_def:
  buffer_length b = b.len
End

(* size bytes starting at offset, zero past the end *)
Definition buffer_read_def:
  buffer_read offset size b =
  if b.len ≤ offset then REPLICATE size (0w:byte) else
  let n = MIN size (b.len - offset) in
  read_bytes b.words offset n (REPLICATE (size - n) 0w)
End

Definition buffer_to_list_def:
  buffer_to_list b = buffer_read 0 b.len b
End

(* bytes written over the buffer starting at offset *)
Definition buffer_write_def:
  buffer_write offset bytes b =
  let n = LENGTH bytes in
  let p = write_bytes b.words b.nonzero offset n bytes in
  <| len := MAX b.len (offset + n); words := FST p; nonzero := SND p |>
End

Definition buffer_of_list_def:
  buffer_of_list bytes = buffer_write 0 bytes empty_buffer
End

(* the size bytes starting at offset, as a buffer of length size *)
Definition buffer_sub_def:
  buffer_sub offset size b =
  if b.len ≤ offset then empty_buffer with len := size else
  let p = if b.nonzero ≤ size DIV 32
          then sub_by_entries offset size (toAList b.words) LN 0
          else sub_by_lookup b.words offset size 0 LN 0 in
  <| len := size; words := FST p; nonzero := SND p |>
End

(* n zero bytes added at the end *)
Definition buffer_extend_def:
  buffer_extend n b = b with len := b.len + n
End

(* list characterizations *)

Definition byte_of_def:
  byte_of (x:num) (k:num) = (n2w ((x DIV 256 ** k) MOD 256) : byte)
End

Theorem small_bytes_of_num_GENLIST:
  ∀n x acc. small_bytes_of_num n x acc = GENLIST (byte_of x) n ++ acc
Proof
  ho_match_mp_tac small_bytes_of_num_ind \\ rw[]
  \\ rw[Once small_bytes_of_num_def]
  \\ Cases_on ‘n’ \\ gvs[GENLIST_CONS]
  \\ rw[byte_of_def, LIST_EQ_REWRITE, EXP, DIV_DIV_DIV_MULT]
QED

Theorem byte_of_MOD:
  ∀m k x. k < m ⇒ byte_of (x MOD 256 ** m) k = byte_of x k
Proof
  rw[byte_of_def]
  \\ ‘∃d. m = k + SUC d’ by (qexists_tac ‘m - k - 1’ \\ simp[])
  \\ gvs[EXP_ADD, GSYM DIV_MOD_MOD_DIV]
  \\ simp[EXP, MOD_MULT_MOD]
QED

Theorem byte_of_DIV:
  ∀m k x. byte_of (x DIV 256 ** m) k = byte_of x (m + k)
Proof
  rw[byte_of_def, EXP_ADD, DIV_DIV_DIV_MULT]
QED

Theorem GENLIST_byte_of_split:
  ∀x m n. GENLIST (byte_of x) (n + m) =
          GENLIST (byte_of (x MOD 256 ** m)) m ++
          GENLIST (byte_of (x DIV 256 ** m)) n
Proof
  rw[GENLIST_APPEND]
  \\ dep_rewrite.DEP_REWRITE_TAC[APPEND_LENGTH_EQ] \\ simp[]
  \\ rw[GENLIST_FUN_EQ, byte_of_MOD, byte_of_DIV]
QED

Theorem bytes_of_num_GENLIST:
  ∀n x acc. bytes_of_num n x acc = GENLIST (byte_of x) n ++ acc
Proof
  ho_match_mp_tac bytes_of_num_ind \\ rpt strip_tac
  \\ Cases_on ‘n ≤ 7’
  >- (once_rewrite_tac[bytes_of_num_def]
      \\ asm_rewrite_tac[small_bytes_of_num_GENLIST])
  \\ first_x_assum drule \\ strip_tac
  \\ ‘(2:num) ** 56 = 256 ** 7’ by simp[]
  \\ once_rewrite_tac[bytes_of_num_def]
  \\ asm_rewrite_tac[small_bytes_of_num_GENLIST]
  \\ ‘n = (n - 7) + 7’ by simp[]
  \\ qpat_x_assum ‘n = _’
       (fn th => CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [th])))
  \\ rewrite_tac[GENLIST_byte_of_split, APPEND_ASSOC]
QED

Theorem read_bytes_GENLIST:
  ∀ws offset n acc.
    read_bytes ws offset n acc =
    GENLIST (λk. byte_of (word_at ws ((offset + k) DIV 32))
                         ((offset + k) MOD 32)) n ++ acc
Proof
  ho_match_mp_tac read_bytes_ind \\ rpt strip_tac
  \\ simp[Once read_bytes_def] \\ IF_CASES_TAC \\ gvs[]
  \\ qmatch_goalsub_abbrev_tac ‘bytes_of_num c’
  \\ ‘c ≤ n ∧ c ≤ 32 - offset MOD 32’ by simp[Abbr‘c’]
  \\ ‘n = (n - c) + c’ by simp[]
  \\ qpat_x_assum ‘n = _’
       (fn th => CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [th])))
  \\ rewrite_tac[bytes_of_num_GENLIST, GENLIST_APPEND, APPEND_ASSOC]
  \\ dep_rewrite.DEP_REWRITE_TAC[APPEND_LENGTH_EQ]
  \\ simp[GENLIST_FUN_EQ, byte_of_DIV] \\ rw[]
  \\ ‘(offset + k) DIV 32 = offset DIV 32 ∧
      (offset + k) MOD 32 = offset MOD 32 + k’ by intLib.ARITH_TAC
  \\ gvs[Once ADD_COMM]
QED

Theorem buffer_read_take_pad_0:
  buffer_read offset sz b = take_pad_0 sz (DROP offset (buffer_to_list b))
Proof
  rw[buffer_to_list_def, buffer_read_def, read_bytes_GENLIST,
     take_pad_0_def, LIST_EQ_REWRITE, PAD_RIGHT, EL_APPEND_EQN,
     DROP_GENLIST, EL_TAKE, EL_REPLICATE, MIN_DEF]
  \\ gvs[EL_APPEND_EQN, EL_TAKE, EL_REPLICATE, EL_GENLIST, LENGTH_TAKE_EQ]
  \\ rw[] \\ gvs[]
QED

Theorem MOD_32_lt[local]:
  ∀x. 0 < 32 − x MOD 32 ∧ x MOD 32 < 32n
Proof
  rw[] \\ ‘x MOD 32 < 32’ by simp[] \\ simp[]
QED

fun cv_measure_tac q =
  WF_REL_TAC q
  \\ rpt strip_tac \\ Cases_on ‘cv_n’ \\ TRY (Cases_on ‘cv_offset’)
  \\ gvs[cvTheory.c2b_def, cv_primTheory.cv_min_def]
  \\ rpt (pop_assum mp_tac) \\ rw[] \\ gvs[MOD_32_lt]
  \\ TRY intLib.ARITH_TAC;

val () = cv_auto_trans_rec small_bytes_of_num_def
  (cv_measure_tac ‘measure (cv$c2n o FST)’);
val () = cv_auto_trans_rec bytes_of_num_def
  (cv_measure_tac ‘measure (cv$c2n o FST)’);
val () = cv_auto_trans num_of_bytes_def;
val () = cv_auto_trans word_at_def;
val () = cv_auto_trans set_word_def;
val () = cv_auto_trans_rec read_bytes_def
  (cv_measure_tac ‘measure (cv$c2n o FST o SND o SND)’);
val () = cv_auto_trans_rec write_bytes_def
  (cv_measure_tac ‘measure (cv$c2n o FST o SND o SND o SND)’);
val () = cv_auto_trans read_word_def;
val sub_by_lookup_pre_def = cv_auto_trans_pre_rec "sub_by_lookup_pre"
  sub_by_lookup_def (cv_measure_tac ‘measure (cv$c2n o FST o SND o SND)’);

Theorem sub_by_lookup_pre[cv_pre]:
  ∀ws offset n q acc nz. sub_by_lookup_pre ws offset n q acc nz
Proof
  ho_match_mp_tac sub_by_lookup_ind \\ rw[]
  \\ rw[Once sub_by_lookup_pre_def]
QED
val () = cv_auto_trans add_bytes_def;
val () = cv_auto_trans sub_by_entries_def;
val () = cv_auto_trans empty_buffer_def;
val () = cv_auto_trans buffer_length_def;
val () = cv_auto_trans buffer_read_def;
val () = cv_auto_trans buffer_to_list_def;
val () = cv_auto_trans buffer_write_def;
val () = cv_auto_trans buffer_of_list_def;
val () = cv_auto_trans buffer_sub_def;
val () = cv_auto_trans buffer_extend_def;
