Theory vfmBuffer
Ancestors
  arithmetic list rich_list words sptree vfmTypes
Libs
  cv_transLib intLib wordsLib dep_rewrite

(* A byte list with constant-time length and logarithmic-time access, used
   for memory and call data so that executing the semantics does not copy
   long lists.  The operations below are characterised by what they do to
   buffer_to_list (see the list equations at the end), so proofs can treat a
   buffer as the byte list it stands for.

   Bytes are grouped into 32-byte words: word i holds bytes 32 * i to
   32 * i + 31, byte 32 * i + j being digit j of the word in base 256.  Zero
   words need not be stored.  Bytes at or past len are not part of the list;
   the operations that lengthen the buffer zero them first. *)

Datatype:
  buffer = <| len : num; words : num num_map |>
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

Definition set_word_def:
  set_word ws i (x:num) = if x = 0 then delete i ws else insert i x ws
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
  write_bytes ws (offset:num) (n:num) (bs:byte list) =
  if n = 0 then ws else
  let i = offset DIV 32 in
  let j = offset MOD 32 in
  let c = MIN n (32 - j) in
  let old = word_at ws i in
  let new = old MOD 256 ** j + 256 ** j * num_of_bytes (TAKE c bs)
            + 256 ** (j + c) * (old DIV 256 ** (j + c)) in
    write_bytes (set_word ws i new) (offset + c) (n - c) (DROP c bs)
Termination
  WF_REL_TAC ‘measure (FST o SND o SND)’ \\ rw[MIN_DEF]
  \\ irule (DECIDE “a < 32n ⇒ 0 < 32 − a”) \\ simp[]
End

(* delete k words starting at word i *)
Definition clear_words_def:
  clear_words ws (i:num) (k:num) =
  if k = 0 then ws else clear_words (delete i ws) (i + 1) (k - 1)
End

(* zero the bytes from byte p up to byte q *)
Definition zero_bytes_def:
  zero_bytes ws (p:num) (q:num) =
  let i = p DIV 32 in
  let ws = if p MOD 32 = 0 then ws
           else set_word ws i (word_at ws i MOD 256 ** (p MOD 32)) in
  let first = (p + 31) DIV 32 in
    clear_words ws first ((q + 31) DIV 32 - first)
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

(* add the words of the n bytes starting at offset to acc, from word q on *)
Definition sub_words_def:
  sub_words ws (offset:num) (n:num) (q:num) acc =
  if n = 0 then acc else
  let c = MIN n 32 in
  let v = read_word ws offset c in
  sub_words ws (offset + c) (n - c) (q + 1)
    (if v = 0 then acc else insert q v acc)
Termination
  WF_REL_TAC ‘measure (FST o SND o SND)’ \\ rw[MIN_DEF]
End

Definition empty_buffer_def:
  empty_buffer = <| len := 0; words := LN |>
End

Definition buffer_length_def:
  buffer_length b = b.len
End

Definition buffer_to_list_def:
  buffer_to_list b = read_bytes b.words 0 b.len []
End

(* size bytes starting at offset, zero past the end *)
Definition buffer_read_def:
  buffer_read offset size b =
  let n = MIN size (b.len - offset) in
  read_bytes b.words offset n (REPLICATE (size - n) (0w:byte))
End

(* at most size bytes starting at offset, stopping at the end *)
Definition buffer_take_def:
  buffer_take offset size b =
  read_bytes b.words offset (MIN size (b.len - offset)) []
End

(* at most size bytes starting at offset, stopping at the end, as a
   buffer *)
Definition buffer_sub_def:
  buffer_sub offset size b =
  let n = MIN size (b.len - offset) in
  <| len := n; words := sub_words b.words offset n 0 LN |>
End

(* n zero bytes added at the end *)
Definition buffer_extend_def:
  buffer_extend n b =
  if n = 0 then b else
  <| len := b.len + n; words := zero_bytes b.words b.len (b.len + n) |>
End

(* bytes written over the buffer starting at offset, after extending it
   with zeros if it is too short *)
Definition buffer_write_def:
  buffer_write offset bytes b =
  let n = LENGTH bytes in
  let b = buffer_extend (offset + n - b.len) b in
  b with words := write_bytes b.words offset n bytes
End

Definition buffer_of_list_def:
  buffer_of_list bytes = buffer_write 0 bytes empty_buffer
End

(* Correctness: the list equations *)

Definition byte_of_def:
  byte_of (x:num) (k:num) = (n2w ((x DIV 256 ** k) MOD 256) : byte)
End

Definition byte_at_def:
  byte_at ws (p:num) = byte_of (word_at ws (p DIV 32)) (p MOD 32)
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
  ∀m k x. byte_of (x MOD 256 ** m) k = if k < m then byte_of x k else 0w
Proof
  rw[byte_of_def]
  >- (‘∃d. m = k + SUC d’ by (qexists_tac ‘m - k - 1’ \\ simp[])
      \\ gvs[EXP_ADD, GSYM DIV_MOD_MOD_DIV]
      \\ simp[EXP, MOD_MULT_MOD])
  \\ ‘x MOD 256 ** m < 256 ** k’ suffices_by simp[LESS_DIV_EQ_ZERO]
  \\ irule LESS_LESS_EQ_TRANS \\ qexists_tac ‘256 ** m’ \\ simp[]
QED

Theorem byte_of_DIV:
  ∀m k x. byte_of (x DIV 256 ** m) k = byte_of x (m + k)
Proof
  rw[byte_of_def, EXP_ADD, DIV_DIV_DIV_MULT]
QED

Theorem byte_of_0[simp]:
  byte_of 0 k = 0w
Proof
  rw[byte_of_def, ZERO_DIV]
QED

(* the digits of a + 256 ** j * b, when a has at most j digits *)
Theorem byte_of_add_mul:
  ∀a b j k. a < 256 ** j ⇒
    byte_of (a + 256 ** j * b) k =
    if k < j then byte_of a k else byte_of b (k - j)
Proof
  rw[]
  >- (‘∃d. j = k + SUC d’ by (qexists_tac ‘j - k - 1’ \\ simp[])
      \\ gvs[] \\ rw[byte_of_def]
      \\ ‘(a + b * 256 ** (k + SUC d)) DIV 256 ** k =
          256 * (256 ** d * b) + a DIV 256 ** k’
           by (‘a + b * 256 ** (k + SUC d) = (256 * (256 ** d * b)) * 256 ** k + a’
                 by simp[EXP_ADD, EXP]
               \\ pop_assum SUBST1_TAC \\ simp[ADD_DIV_ADD_DIV])
      \\ pop_assum SUBST1_TAC
      \\ qspecl_then [‘a DIV 256 ** k’, ‘256 ** d * b’] mp_tac
           (intLib.ARITH_PROVE “∀y x. (256 * x + y) MOD 256 = y MOD 256n”)
      \\ simp[])
  \\ ‘k = j + (k - j)’ by simp[]
  \\ pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th])))
  \\ rw[GSYM byte_of_DIV]
  \\ ‘(a + 256 ** j * b) DIV 256 ** j = b’ suffices_by simp[]
  \\ once_rewrite_tac[ADD_COMM] \\ once_rewrite_tac[MULT_COMM]
  \\ simp[ADD_DIV_ADD_DIV, LESS_DIV_EQ_ZERO]
QED

Theorem byte_of_mul_add:
  ∀a b j k. a < 256 ** j ⇒
    byte_of (256 ** j * b + a) k =
    if k < j then byte_of a k else byte_of b (k - j)
Proof
  metis_tac[byte_of_add_mul, ADD_COMM]
QED

Theorem GENLIST_byte_of_split:
  ∀x m n. GENLIST (byte_of x) (n + m) =
          GENLIST (byte_of (x MOD 256 ** m)) m ++
          GENLIST (byte_of (x DIV 256 ** m)) n
Proof
  rw[GENLIST_APPEND]
  \\ DEP_REWRITE_TAC[APPEND_LENGTH_EQ] \\ simp[]
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

Theorem num_of_bytes_lt:
  ∀bs. num_of_bytes bs < 256 ** LENGTH bs
Proof
  Induct \\ rw[num_of_bytes_def, EXP]
  \\ ‘w2n h < 256’ by (assume_tac (INST_TYPE [alpha |-> “:8”] w2n_lt)
                       \\ gvs[dimword_def])
  \\ intLib.ARITH_TAC
QED

Theorem byte_of_num_of_bytes:
  ∀bs k. byte_of (num_of_bytes bs) k =
         if k < LENGTH bs then EL k bs else 0w
Proof
  Induct \\ rw[num_of_bytes_def]
  \\ ‘w2n h < 256 ** 1’ by (assume_tac (INST_TYPE [alpha |-> “:8”] w2n_lt)
                            \\ gvs[dimword_def])
  \\ drule byte_of_add_mul \\ simp[]
  \\ disch_then kall_tac
  \\ Cases_on ‘k’ \\ gvs[byte_of_def]
QED

Theorem word_at_set_word:
  word_at (set_word ws i x) j = if j = i then x else word_at ws j
Proof
  rw[word_at_def, set_word_def, lookup_insert, lookup_delete]
QED

Theorem byte_at_set_word:
  byte_at (set_word ws i x) p =
  if p DIV 32 = i then byte_of x (p MOD 32) else byte_at ws p
Proof
  rw[byte_at_def, word_at_set_word]
QED

Theorem read_bytes_GENLIST:
  ∀ws offset n acc.
    read_bytes ws offset n acc =
    GENLIST (λk. byte_at ws (offset + k)) n ++ acc
Proof
  ho_match_mp_tac read_bytes_ind \\ rpt strip_tac
  \\ simp[Once read_bytes_def] \\ IF_CASES_TAC \\ gvs[]
  \\ qmatch_goalsub_abbrev_tac ‘bytes_of_num c’
  \\ ‘c ≤ n ∧ c ≤ 32 - offset MOD 32’ by simp[Abbr‘c’]
  \\ ‘n = (n - c) + c’ by simp[]
  \\ qpat_x_assum ‘n = _’
       (fn th => CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [th])))
  \\ rewrite_tac[bytes_of_num_GENLIST, GENLIST_APPEND, APPEND_ASSOC]
  \\ DEP_REWRITE_TAC[APPEND_LENGTH_EQ]
  \\ simp[GENLIST_FUN_EQ, byte_of_DIV, byte_at_def] \\ rw[]
  \\ ‘(offset + k) DIV 32 = offset DIV 32 ∧
      (offset + k) MOD 32 = offset MOD 32 + k’ by intLib.ARITH_TAC
  \\ gvs[Once ADD_COMM]
QED

Theorem write_bytes_arith[local]:
  ∀offset c p. c ≤ 32 − offset MOD 32 ⇒
    (p DIV 32 = offset DIV 32 ⇒
     (offset MOD 32 ≤ p MOD 32 ∧ p MOD 32 < c + offset MOD 32 ⇔
      offset ≤ p ∧ p < offset + c) ∧
     p MOD 32 − offset MOD 32 = p − offset) ∧
    (p DIV 32 ≠ offset DIV 32 ⇒ ¬(offset ≤ p ∧ p < offset + c))
Proof
  rpt gen_tac \\ strip_tac \\ conj_tac \\ strip_tac \\ intLib.ARITH_TAC
QED

Theorem write_bytes_byte_at:
  ∀ws offset n bs p.
    n ≤ LENGTH bs ⇒
    byte_at (write_bytes ws offset n bs) p =
    if offset ≤ p ∧ p < offset + n then EL (p - offset) bs
    else byte_at ws p
Proof
  ho_match_mp_tac write_bytes_ind \\ rpt strip_tac
  \\ simp[Once write_bytes_def] \\ IF_CASES_TAC \\ gvs[]
  \\ qmatch_goalsub_abbrev_tac ‘DROP c bs’
  \\ ‘c ≤ n ∧ c ≤ 32 - offset MOD 32 ∧ 0 < c’
       by (simp[Abbr‘c’, MIN_DEF] \\ rw[]
           \\ ‘offset MOD 32 < 32’ by simp[] \\ simp[])
  \\ simp[byte_at_set_word]
  \\ qmatch_goalsub_abbrev_tac ‘byte_of new’
  \\ ‘∀k. byte_of new k =
          if offset MOD 32 ≤ k ∧ k < offset MOD 32 + c
          then EL (k - offset MOD 32) bs
          else byte_of (word_at ws (offset DIV 32)) k’
       by (qabbrev_tac ‘j = offset MOD 32’
           \\ qabbrev_tac ‘old = word_at ws (offset DIV 32)’
           \\ ‘num_of_bytes (TAKE c bs) < 256 ** c’
                by (qspec_then ‘TAKE c bs’ mp_tac num_of_bytes_lt \\ simp[])
           \\ ‘old MOD 256 ** j < 256 ** j’ by simp[]
           \\ ‘new = old MOD 256 ** j + 256 ** j *
                 (num_of_bytes (TAKE c bs) +
                  256 ** c * (old DIV 256 ** (j + c)))’
                by simp[Abbr‘new’, EXP_ADD, LEFT_ADD_DISTRIB]
           \\ pop_assum SUBST1_TAC \\ gen_tac
           \\ DEP_REWRITE_TAC[byte_of_add_mul] \\ simp[]
           \\ rw[byte_of_num_of_bytes, byte_of_MOD, byte_of_DIV, EL_TAKE]
           \\ gvs[])
  \\ qpat_x_assum ‘∀p. byte_at (write_bytes _ _ _ _) _ = _’
       (fn th => rewrite_tac[th])
  \\ simp[byte_at_set_word]
  \\ Cases_on ‘offset + c ≤ p ∧ p < offset + n’
  >- gvs[EL_DROP]
  \\ drule_then (qspec_then ‘p’ strip_assume_tac) write_bytes_arith
  \\ Cases_on ‘p DIV 32 = offset DIV 32’ \\ gvs[]
  >- (rw[] \\ gvs[byte_at_def])
  \\ rw[] \\ gvs[byte_at_def]
QED

Theorem word_at_clear_words:
  ∀ws i k j. word_at (clear_words ws i k) j =
             if i ≤ j ∧ j < i + k then 0 else word_at ws j
Proof
  ho_match_mp_tac clear_words_ind \\ rw[]
  \\ rw[Once clear_words_def] \\ gvs[]
  \\ rw[word_at_def, lookup_delete] \\ gvs[]
QED

Theorem zero_bytes_byte_at:
  p' < q ⇒
  byte_at (zero_bytes ws p q) p' = if p' < p then byte_at ws p' else 0w
Proof
  rw[zero_bytes_def, byte_at_def, word_at_clear_words, word_at_set_word]
  \\ rw[byte_of_MOD] \\ gvs[] \\ rw[]
  \\ ‘F’ suffices_by simp[] \\ intLib.ARITH_TAC
QED

Theorem byte_at_same_word:
  k < 32 - offset MOD 32 ⇒
  byte_at ws (k + offset) =
  byte_of (word_at ws (offset DIV 32)) (offset MOD 32 + k)
Proof
  rw[byte_at_def]
  \\ ‘(k + offset) DIV 32 = offset DIV 32 ∧
      (k + offset) MOD 32 = offset MOD 32 + k’ by intLib.ARITH_TAC
  \\ simp[]
QED

Theorem byte_at_next_word:
  32 - offset MOD 32 ≤ k ∧ k < 64 - offset MOD 32 ⇒
  byte_at ws (k + offset) =
  byte_of (word_at ws (offset DIV 32 + 1)) (k - (32 - offset MOD 32))
Proof
  rw[byte_at_def]
  \\ ‘(k + offset) DIV 32 = offset DIV 32 + 1 ∧
      (k + offset) MOD 32 = k - (32 - offset MOD 32)’ by intLib.ARITH_TAC
  \\ simp[]
QED

Theorem byte_of_read_word:
  c ≤ 32 ⇒
  byte_of (read_word ws offset c) k =
  if k < c then byte_at ws (offset + k) else 0w
Proof
  strip_tac \\ simp[read_word_def]
  \\ ‘offset MOD 32 < 32’ by simp[]
  \\ qabbrev_tac ‘m = MIN c (32 - offset MOD 32)’
  \\ ‘m ≤ c ∧ m ≤ 32 - offset MOD 32’ by simp[Abbr‘m’]
  \\ ‘∀x. x MOD 256 ** m < 256 ** m’ by simp[]
  \\ IF_CASES_TAC
  >- (‘m = 32 - offset MOD 32’ by gvs[Abbr‘m’, MIN_DEF]
      \\ DEP_REWRITE_TAC[byte_of_mul_add] \\ simp[]
      \\ Cases_on ‘k < m’
      >- simp[byte_of_MOD, byte_of_DIV, byte_at_same_word]
      \\ Cases_on ‘k < c’
      \\ simp[byte_of_MOD, byte_of_DIV, byte_at_next_word])
  \\ ‘m = c’ by gvs[Abbr‘m’, MIN_DEF]
  \\ Cases_on ‘k < c’
  \\ simp[byte_of_MOD, byte_of_DIV, byte_at_same_word]
QED

Theorem sub_words_arith[local]:
  ∀q p n c offset. c = MIN n 32 ∧ n ≠ 0 ⇒
   (32 * (q + 1) ≤ p ∧ p < 32 * (q + 1) + (n − c) ⇒
    32 * q ≤ p ∧ p < 32 * q + n ∧
    offset + c + (p − 32 * (q + 1)) = offset + (p − 32 * q)) ∧
   (¬(32 * (q + 1) ≤ p ∧ p < 32 * (q + 1) + (n − c)) ⇒
    (p DIV 32 = q ⇒
     32 * q ≤ p ∧ (p < 32 * q + n ⇔ p MOD 32 < c) ∧
     p − 32 * q = p MOD 32) ∧
    (p DIV 32 ≠ q ⇒ ¬(32 * q ≤ p ∧ p < 32 * q + n)))
Proof
  rpt gen_tac \\ strip_tac \\ gvs[MIN_DEF]
  \\ rpt conj_tac \\ rpt strip_tac \\ intLib.ARITH_TAC
QED

Theorem sub_words_byte_at:
  ∀ws offset n q acc p.
    (∀i. q ≤ i ⇒ word_at acc i = 0) ⇒
    byte_at (sub_words ws offset n q acc) p =
    if 32 * q ≤ p ∧ p < 32 * q + n then byte_at ws (offset + (p - 32 * q))
    else byte_at acc p
Proof
  ho_match_mp_tac sub_words_ind \\ rpt strip_tac
  \\ simp[Once sub_words_def] \\ IF_CASES_TAC \\ gvs[]
  \\ qmatch_goalsub_abbrev_tac ‘read_word ws offset c’
  \\ qmatch_goalsub_abbrev_tac ‘sub_words ws _ _ _ acc'’
  \\ ‘c ≤ 32 ∧ 0 < c’ by simp[Abbr‘c’]
  \\ ‘∀i. word_at acc' i =
          if i = q then read_word ws offset c else word_at acc i’
       by (rw[Abbr‘acc'’, word_at_def, lookup_insert] \\ gvs[word_at_def])
  \\ ‘∀i. q + 1 ≤ i ⇒ word_at acc' i = 0’ by simp[]
  \\ first_x_assum drule \\ disch_then (fn th => rewrite_tac[th])
  \\ qspecl_then [‘q’,‘p’,‘n’,‘c’,‘offset’] mp_tac sub_words_arith
  \\ impl_tac >- simp[Abbr‘c’]
  \\ strip_tac
  \\ Cases_on ‘32 * (q + 1) ≤ p ∧ p < 32 * (q + 1) + (n − c)’
  >- gvs[]
  \\ asm_rewrite_tac[]
  \\ simp[byte_at_def]
  \\ Cases_on ‘p DIV 32 = q’ \\ gvs[byte_of_read_word]
  \\ rw[] \\ gvs[] \\ simp[byte_at_def]
  \\ ‘offset + p − 32 * (p DIV 32) = offset + p MOD 32’
       by (qpat_x_assum ‘32 * _ ≤ p’ mp_tac
           \\ qpat_x_assum ‘p − _ = _’ mp_tac
           \\ rpt (pop_assum kall_tac) \\ intLib.ARITH_TAC)
  \\ simp[]
QED

Theorem buffer_to_list_GENLIST:
  buffer_to_list b = GENLIST (byte_at b.words) b.len
Proof
  rw[buffer_to_list_def, read_bytes_GENLIST]
  \\ simp[GENLIST_FUN_EQ]
QED

Theorem LENGTH_buffer_to_list[simp]:
  LENGTH (buffer_to_list b) = buffer_length b
Proof
  rw[buffer_to_list_GENLIST, buffer_length_def]
QED

Theorem buffer_to_list_empty[simp]:
  buffer_to_list empty_buffer = []
Proof
  rw[buffer_to_list_def, empty_buffer_def, Once read_bytes_def]
QED

Theorem buffer_length_empty[simp]:
  buffer_length empty_buffer = 0
Proof
  rw[buffer_length_def, empty_buffer_def]
QED

Theorem buffer_read_to_list:
  buffer_read offset sz b = take_pad_0 sz (DROP offset (buffer_to_list b))
Proof
  rw[buffer_length_def, buffer_to_list_GENLIST, buffer_read_def, read_bytes_GENLIST,
     take_pad_0_def, LIST_EQ_REWRITE, PAD_RIGHT, EL_APPEND_EQN,
     DROP_GENLIST, EL_TAKE, EL_REPLICATE, MIN_DEF]
  \\ gvs[buffer_length_def, EL_APPEND_EQN, EL_TAKE, EL_REPLICATE, EL_GENLIST, LENGTH_TAKE_EQ]
  \\ rw[] \\ gvs[buffer_length_def]
QED

Theorem buffer_take_to_list:
  buffer_take offset sz b = TAKE sz (DROP offset (buffer_to_list b))
Proof
  rw[buffer_length_def, buffer_to_list_GENLIST, buffer_take_def, read_bytes_GENLIST,
     LIST_EQ_REWRITE, DROP_GENLIST, EL_TAKE, MIN_DEF, LENGTH_TAKE_EQ]
  \\ gvs[buffer_length_def]
QED

Theorem buffer_to_list_sub:
  buffer_to_list (buffer_sub offset sz b) =
  TAKE sz (DROP offset (buffer_to_list b))
Proof
  rw[buffer_length_def, buffer_to_list_GENLIST, buffer_sub_def, LIST_EQ_REWRITE, DROP_GENLIST,
     EL_TAKE, LENGTH_TAKE_EQ]
  \\ DEP_REWRITE_TAC[sub_words_byte_at]
  \\ simp[word_at_def, lookup_def]
  \\ gvs[buffer_length_def, MIN_DEF] \\ rw[] \\ gvs[buffer_length_def]
QED

Theorem buffer_length_sub[simp]:
  buffer_length (buffer_sub offset sz b) = MIN sz (buffer_length b - offset)
Proof
  rw[buffer_sub_def, buffer_length_def]
QED

Theorem buffer_to_list_extend:
  buffer_to_list (buffer_extend n b) = buffer_to_list b ++ REPLICATE n 0w
Proof
  rw[buffer_length_def, buffer_extend_def, buffer_to_list_GENLIST, LIST_EQ_REWRITE,
     EL_APPEND_EQN, EL_REPLICATE, zero_bytes_byte_at]
QED

Theorem buffer_length_extend[simp]:
  buffer_length (buffer_extend n b) = buffer_length b + n
Proof
  rw[buffer_extend_def, buffer_length_def]
QED

Theorem buffer_to_list_write:
  buffer_to_list (buffer_write offset bs b) =
  TAKE offset (PAD_RIGHT 0w offset (buffer_to_list b)) ++ bs ++
  DROP (offset + LENGTH bs) (buffer_to_list b)
Proof
  simp[buffer_length_def]
  \\ qabbrev_tac ‘b' = buffer_extend (offset + LENGTH bs - b.len) b’
  \\ ‘buffer_to_list b' =
      buffer_to_list b ++ REPLICATE (offset + LENGTH bs - b.len) 0w’
       by simp[Abbr‘b'’, buffer_to_list_extend]
  \\ ‘b'.len = MAX b.len (offset + LENGTH bs)’
       by (simp[Abbr‘b'’, buffer_extend_def] \\ rw[MAX_DEF])
  \\ fs[buffer_to_list_GENLIST]
  \\ rw[buffer_write_def, LIST_EQ_REWRITE, write_bytes_byte_at,
        EL_APPEND_EQN, EL_TAKE, EL_DROP, PAD_RIGHT, EL_REPLICATE,
        LENGTH_TAKE_EQ, MAX_DEF]
  \\ qpat_x_assum ‘GENLIST _ _ = _’
       (mp_tac o Q.AP_TERM ‘EL x’)
  \\ rw[EL_APPEND_EQN, EL_REPLICATE] \\ gvs[buffer_length_def]
QED

Theorem buffer_length_write[simp]:
  buffer_length (buffer_write offset bs b) =
  MAX (buffer_length b) (offset + LENGTH bs)
Proof
  rw[buffer_write_def, buffer_extend_def, buffer_length_def, MAX_DEF]
QED

Theorem buffer_to_list_write_le:
  offset ≤ buffer_length b ⇒
  buffer_to_list (buffer_write offset bs b) =
  TAKE offset (buffer_to_list b) ++ bs ++
  DROP (offset + LENGTH bs) (buffer_to_list b)
Proof
  rw[buffer_to_list_write, PAD_RIGHT]
  \\ ‘offset − buffer_length b = 0’ by simp[] \\ simp[]
QED

Theorem buffer_to_list_of_list[simp]:
  buffer_to_list (buffer_of_list bs) = bs
Proof
  rw[buffer_of_list_def, buffer_to_list_write_le]
QED

Theorem buffer_length_of_list[simp]:
  buffer_length (buffer_of_list bs) = LENGTH bs
Proof
  rw[buffer_of_list_def]
QED

(* cv translation *)

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
  (cv_measure_tac ‘measure (cv$c2n o FST o SND o SND)’);
val () = cv_auto_trans clear_words_def;
val () = cv_auto_trans zero_bytes_def;
val () = cv_auto_trans read_word_def;
val sub_words_pre_def = cv_auto_trans_pre_rec "sub_words_pre"
  sub_words_def (cv_measure_tac ‘measure (cv$c2n o FST o SND o SND)’);

Theorem sub_words_pre[cv_pre]:
  ∀ws offset n q acc. sub_words_pre ws offset n q acc
Proof
  ho_match_mp_tac sub_words_ind \\ rw[]
  \\ rw[Once sub_words_pre_def]
QED
val () = cv_auto_trans empty_buffer_def;
val () = cv_auto_trans buffer_length_def;
val () = cv_auto_trans buffer_to_list_def;
val () = cv_auto_trans buffer_read_def;
val () = cv_auto_trans buffer_take_def;
val () = cv_auto_trans buffer_sub_def;
val () = cv_auto_trans buffer_extend_def;
val () = cv_auto_trans buffer_write_def;
val () = cv_auto_trans buffer_of_list_def;
