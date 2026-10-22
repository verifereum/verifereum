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

(* old with its c bytes from byte j on replaced by the first c bytes of bs *)
Definition splice_bytes_def:
  splice_bytes (old:num) (j:num) (c:num) (bs:byte list) =
  old MOD 256 ** j + 256 ** j * num_of_bytes (TAKE c bs)
  + 256 ** (j + c) * (old DIV 256 ** (j + c))
End

(* write the first n bytes of bs starting at byte offset *)
Definition write_bytes_def:
  write_bytes ws (offset:num) (n:num) (bs:byte list) =
  if n = 0 then ws else
  let i = offset DIV 32 in
  let j = offset MOD 32 in
  let c = MIN n (32 - j) in
    write_bytes (set_word ws i (splice_bytes (word_at ws i) j c bs))
      (offset + c) (n - c) (DROP c bs)
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

(* word q of the n bytes starting at byte offset *)
Definition out_word_def:
  out_word ws (offset:num) (n:num) (q:num) =
  read_word ws (offset + 32 * q) (MIN 32 (n - 32 * q))
End

Definition put_word_def:
  put_word ws offset n q acc =
  let v = out_word ws offset n q in
  if v = 0 then acc else insert q v acc
End

(* add words q to q + k - 1 of the n bytes starting at offset to acc *)
Definition sub_words_def:
  sub_words ws offset n q (k:num) acc =
  if k = 0 then acc
  else sub_words ws offset n (q + 1) (k - 1) (put_word ws offset n q acc)
End

(* the same for the words that can be nonzero, given the stored words kvs:
   stored word i holds bytes of words i - offset DIV 32 - 1 and
   i - offset DIV 32 *)
Definition sparse_words_def:
  sparse_words ws offset n [] acc = acc ∧
  sparse_words ws offset n ((i:num,v:num)::kvs) acc =
  let i0 = offset DIV 32 in
  let acc = if i0 < i then put_word ws offset n (i - i0 - 1) acc else acc in
  let acc = if i0 ≤ i then put_word ws offset n (i - i0) acc else acc in
    sparse_words ws offset n kvs acc
End

(* the number of values stored in t if it is at most k, and otherwise some
   number above k, found without visiting many more than k values *)
Definition size_upto_def:
  size_upto LN (k:num) = 0n ∧
  size_upto (LS _) k = 1 ∧
  size_upto (BN l r) k =
    (let a = size_upto l k in if k < a then a else a + size_upto r (k - a)) ∧
  size_upto (BS l _ r) k =
    (let a = size_upto l k + 1 in
     if k < a then a else a + size_upto r (k - a))
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

(* sz bytes starting at offset, zero past the end *)
Definition buffer_read_def:
  buffer_read offset sz b =
  let n = MIN sz (b.len - offset) in
  read_bytes b.words offset n (REPLICATE (sz - n) (0w:byte))
End

(* at most sz bytes starting at offset, stopping at the end *)
Definition buffer_take_def:
  buffer_take offset sz b =
  read_bytes b.words offset (MIN sz (b.len - offset)) []
End

(* at most sz bytes starting at offset, stopping at the end, as a buffer;
   the words are found from the stored words when there are few of those *)
Definition buffer_sub_def:
  buffer_sub offset sz b =
  let n = MIN sz (b.len - offset) in
  let k = (n + 31) DIV 32 in
  <| len := n;
     words := if size_upto b.words k ≤ k
              then sparse_words b.words offset n (toAList b.words) LN
              else sub_words b.words offset n 0 k LN |>
End

(* n zero bytes added at the end *)
Definition buffer_extend_def:
  buffer_extend n b =
  if n = 0 then b else
  <| len := b.len + n; words := zero_bytes b.words b.len (b.len + n) |>
End

(* bytes written over the buffer starting at offset, after extending it
   with zeros if it is too short; writing no bytes changes nothing *)
Definition buffer_write_def:
  buffer_write offset bytes b =
  if bytes = [] then b else
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
           by (‘a + b * 256 ** (k + SUC d) =
                  (256 * (256 ** d * b)) * 256 ** k + a’
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

Theorem byte_of_splice_bytes:
  c ≤ LENGTH bs ⇒
  byte_of (splice_bytes old j c bs) k =
  if j ≤ k ∧ k < j + c then EL (k - j) bs else byte_of old k
Proof
  strip_tac
  \\ ‘num_of_bytes (TAKE c bs) < 256 ** c’
       by (qspec_then ‘TAKE c bs’ mp_tac num_of_bytes_lt \\ simp[])
  \\ ‘old MOD 256 ** j < 256 ** j’ by simp[]
  \\ ‘splice_bytes old j c bs = old MOD 256 ** j + 256 ** j *
        (num_of_bytes (TAKE c bs) + 256 ** c * (old DIV 256 ** (j + c)))’
       by simp[splice_bytes_def, EXP_ADD, LEFT_ADD_DISTRIB]
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[byte_of_add_mul] \\ simp[]
  \\ rw[byte_of_num_of_bytes, byte_of_MOD, byte_of_DIV, EL_TAKE]
  \\ gvs[]
QED

Theorem byte_at_splice[local]:
  c ≤ LENGTH bs ∧ c ≤ 32 − offset MOD 32 ∧ p DIV 32 = offset DIV 32 ⇒
  byte_of (splice_bytes (word_at ws (offset DIV 32)) (offset MOD 32) c bs)
    (p MOD 32) =
  if offset ≤ p ∧ p < offset + c then EL (p - offset) bs else byte_at ws p
Proof
  strip_tac
  \\ drule_then (qspec_then ‘p’ mp_tac) write_bytes_arith
  \\ asm_rewrite_tac[] \\ strip_tac
  \\ simp[byte_of_splice_bytes, byte_at_def]
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
  \\ ‘c ≤ LENGTH bs’ by simp[]
  \\ simp[byte_at_set_word]
  \\ qpat_x_assum ‘∀p. byte_at (write_bytes _ _ _ _) _ = _’
       (fn th => rewrite_tac[th])
  \\ simp[byte_at_set_word, byte_at_splice]
  \\ Cases_on ‘c + offset ≤ p ∧ p < n + offset’
  >- gvs[EL_DROP]
  \\ Cases_on ‘p DIV 32 = offset DIV 32’
  >- (asm_rewrite_tac[] \\ rw[] \\ gvs[])
  \\ drule_then (qspec_then ‘p’ strip_assume_tac) write_bytes_arith
  \\ asm_rewrite_tac[] \\ rw[] \\ gvs[]
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
  rw[buffer_length_def, buffer_to_list_GENLIST, buffer_read_def,
     read_bytes_GENLIST, take_pad_0_def, LIST_EQ_REWRITE, PAD_RIGHT,
     EL_APPEND_EQN, DROP_GENLIST, EL_TAKE, EL_REPLICATE, MIN_DEF]
  \\ gvs[buffer_length_def, EL_APPEND_EQN, EL_TAKE, EL_REPLICATE, EL_GENLIST,
         LENGTH_TAKE_EQ]
  \\ rw[] \\ gvs[buffer_length_def]
QED

Theorem buffer_take_to_list:
  buffer_take offset sz b = TAKE sz (DROP offset (buffer_to_list b))
Proof
  rw[buffer_length_def, buffer_to_list_GENLIST, buffer_take_def,
     read_bytes_GENLIST, LIST_EQ_REWRITE, DROP_GENLIST, EL_TAKE, MIN_DEF,
     LENGTH_TAKE_EQ]
  \\ gvs[buffer_length_def]
QED

Theorem buffer_length_sub[simp]:
  buffer_length (buffer_sub offset sz b) = MIN sz (buffer_length b - offset)
Proof
  rw[buffer_sub_def, buffer_length_def]
QED

Theorem buffer_to_list_extend:
  buffer_to_list (buffer_extend n b) = buffer_to_list b ++ REPLICATE n 0w
Proof
  rw[buffer_length_def, buffer_extend_def, buffer_to_list_GENLIST,
     LIST_EQ_REWRITE, EL_APPEND_EQN, EL_REPLICATE, zero_bytes_byte_at]
QED

Theorem buffer_extend_0[simp]:
  buffer_extend 0 b = b
Proof
  rw[buffer_extend_def]
QED

Theorem buffer_length_extend[simp]:
  buffer_length (buffer_extend n b) = buffer_length b + n
Proof
  rw[buffer_extend_def, buffer_length_def]
QED

Theorem buffer_write_nil[simp]:
  buffer_write offset [] b = b
Proof
  rw[buffer_write_def]
QED

Theorem buffer_to_list_write:
  bs ≠ [] ⇒
  buffer_to_list (buffer_write offset bs b) =
  TAKE offset (PAD_RIGHT 0w offset (buffer_to_list b)) ++ bs ++
  DROP (offset + LENGTH bs) (buffer_to_list b)
Proof
  strip_tac \\ simp[buffer_length_def]
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
  if bs = [] then buffer_length b
  else MAX (buffer_length b) (offset + LENGTH bs)
Proof
  rw[buffer_write_def, buffer_extend_def, buffer_length_def, MAX_DEF]
QED

Theorem buffer_to_list_write_le:
  (bs ≠ [] ⇒ offset ≤ buffer_length b) ⇒
  buffer_to_list (buffer_write offset bs b) =
  TAKE offset (buffer_to_list b) ++ bs ++
  DROP (offset + LENGTH bs) (buffer_to_list b)
Proof
  Cases_on ‘bs = []’ >- simp[TAKE_DROP]
  \\ rw[buffer_to_list_write, PAD_RIGHT]
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

(* buffer_sub builds the same words as buffer_of_list does: a word is
   stored iff it is nonzero, and has no bytes beyond its 32 *)

(* Equality of buffers is equality of representations: two buffers with
   the same buffer_to_list can differ, e.g. by storing a zero word.  The
   buffers the semantics builds are canonical, though: their words are
   good_words, and no byte at or past len is nonzero.  Not yet done: define
   that invariant, show that empty_buffer has it and that buffer_extend,
   buffer_write and buffer_sub keep it, and prove from good_words_eq that
   a buffer with it equals buffer_of_list (buffer_to_list b).  Equality of
   such buffers is then equality of their lists, so a proof can state
   memory as buffer_of_list of a list instead of a term built from
   buffer_write and buffer_extend. *)

Definition good_words_def:
  good_words ws ⇔
    wf ws ∧
    ∀i. lookup i ws ≠ SOME 0 ∧ ∀k. 32 ≤ k ⇒ byte_of (word_at ws i) k = 0w
End

Theorem num_digits_eq:
  ∀x y. (∀k. byte_of x k = byte_of y k) ⇒ x = y
Proof
  ‘∀s x y. x + y = s ∧ (∀k. byte_of x k = byte_of y k) ⇒ x = y’
    suffices_by metis_tac[]
  \\ completeInduct_on ‘s’ \\ rw[]
  \\ Cases_on ‘x + y = 0’ >- gvs[]
  \\ ‘∀z k. byte_of (z DIV 256) k = byte_of z (k + 1)’
       by (rpt gen_tac \\ qspecl_then [‘1’,‘k’,‘z’] mp_tac byte_of_DIV
           \\ simp[])
  \\ ‘x DIV 256 + y DIV 256 < x + y’
       by (qpat_x_assum ‘x + y ≠ 0’ mp_tac \\ rpt (pop_assum kall_tac)
           \\ intLib.ARITH_TAC)
  \\ ‘x DIV 256 = y DIV 256’
       by (first_x_assum drule \\ disch_then irule \\ simp[])
  \\ ‘x MOD 256 = y MOD 256’
       by (qpat_x_assum ‘∀k. byte_of x k = _’ (qspec_then ‘0’ mp_tac)
           \\ rpt (pop_assum kall_tac) \\ simp[byte_of_def])
  \\ metis_tac[DIVISION, DECIDE “0 < 256n”]
QED

Theorem word_at_byte_at:
  k < 32 ⇒ byte_of (word_at ws i) k = byte_at ws (32 * i + k)
Proof
  rw[byte_at_def, LESS_DIV_EQ_ZERO]
QED

Theorem good_words_eq:
  good_words ws1 ∧ good_words ws2 ∧ (∀p. byte_at ws1 p = byte_at ws2 p) ⇒
  ws1 = ws2
Proof
  rw[good_words_def]
  \\ ‘∀i. word_at ws1 i = word_at ws2 i’
       by (gen_tac \\ irule num_digits_eq \\ gen_tac
           \\ Cases_on ‘k < 32’ \\ gvs[NOT_LESS, word_at_byte_at])
  \\ DEP_REWRITE_TAC[spt_eq_thm] \\ rw[]
  \\ first_x_assum (qspec_then ‘n’ mp_tac)
  \\ simp[word_at_def]
  \\ Cases_on ‘lookup n ws1’ \\ Cases_on ‘lookup n ws2’ \\ gvs[]
  \\ metis_tac[]
QED

Theorem good_words_LN:
  good_words LN
Proof
  rw[good_words_def, word_at_def, lookup_def, wf_def]
QED

Theorem good_words_set_word:
  good_words ws ∧ (∀k. 32 ≤ k ⇒ byte_of x k = 0w) ⇒
  good_words (set_word ws i x)
Proof
  rw[good_words_def, word_at_set_word] \\ gvs[]
  \\ rw[set_word_def, wf_insert, wf_delete, lookup_insert, lookup_delete]
  \\ rw[] \\ gvs[]
QED

Theorem good_words_write_bytes:
  ∀ws offset n bs.
    good_words ws ∧ n ≤ LENGTH bs ⇒ good_words (write_bytes ws offset n bs)
Proof
  ho_match_mp_tac write_bytes_ind \\ rpt strip_tac
  \\ simp[Once write_bytes_def] \\ IF_CASES_TAC \\ gvs[]
  \\ qmatch_goalsub_abbrev_tac ‘DROP c bs’
  \\ ‘c ≤ n ∧ c ≤ 32 - offset MOD 32’ by simp[Abbr‘c’]
  \\ first_x_assum irule \\ simp[]
  \\ irule good_words_set_word \\ simp[byte_of_splice_bytes]
  \\ fs[good_words_def]
QED

Theorem clear_words_LN[local]:
  ∀ws i k. ws = LN ⇒ clear_words ws i k = LN
Proof
  ho_match_mp_tac clear_words_ind \\ rw[]
  \\ rw[Once clear_words_def, delete_def]
QED

Theorem buffer_of_list_fields[local]:
  (buffer_of_list bs).len = LENGTH bs ∧
  (buffer_of_list bs).words = write_bytes LN 0 (LENGTH bs) bs
Proof
  Cases_on ‘bs = []’
  >- rw[buffer_of_list_def, empty_buffer_def, Once write_bytes_def]
  \\ rw[buffer_of_list_def, buffer_write_def, buffer_extend_def,
        empty_buffer_def, zero_bytes_def, clear_words_LN]
QED

Theorem byte_at_LN[local]:
  byte_at LN p = 0w
Proof
  rw[byte_at_def, word_at_def, lookup_def]
QED

Theorem div_32_add[local]:
  (offset + 32 * j) DIV 32 = offset DIV 32 + j ∧
  (32 * j + offset) DIV 32 = offset DIV 32 + j ∧
  (offset + 32 * j) MOD 32 = offset MOD 32 ∧
  (32 * j + offset) MOD 32 = offset MOD 32
Proof
  intLib.ARITH_TAC
QED

Theorem out_word_nonzero:
  out_word ws offset n j ≠ 0 ⇒
  (∃v. lookup (offset DIV 32 + j) ws = SOME v) ∨
  (∃v. lookup (offset DIV 32 + j + 1) ws = SOME v)
Proof
  CCONTR_TAC \\ gvs[]
  \\ Cases_on ‘lookup (offset DIV 32 + j) ws’ \\ gvs[]
  \\ Cases_on ‘lookup (offset DIV 32 + j + 1) ws’ \\ gvs[]
  \\ gvs[out_word_def, read_word_def, div_32_add, word_at_def]
QED

Theorem lookup_put_word:
  lookup j (put_word ws offset n q acc) =
  if j = q ∧ out_word ws offset n q ≠ 0 then SOME (out_word ws offset n q)
  else lookup j acc
Proof
  rw[put_word_def, lookup_insert] \\ gvs[]
QED

Theorem wf_put_word:
  wf acc ⇒ wf (put_word ws offset n q acc)
Proof
  rw[put_word_def, wf_insert]
QED

Theorem lookup_sub_words:
  ∀ws offset n q k acc j.
    lookup j (sub_words ws offset n q k acc) =
    if q ≤ j ∧ j < q + k ∧ out_word ws offset n j ≠ 0
    then SOME (out_word ws offset n j) else lookup j acc
Proof
  ho_match_mp_tac sub_words_ind \\ rw[]
  \\ rw[Once sub_words_def, lookup_put_word] \\ gvs[]
  \\ rw[lookup_put_word] \\ gvs[]
  \\ ‘j = q’ by simp[] \\ gvs[]
QED

Theorem wf_sub_words:
  ∀ws offset n q k acc. wf acc ⇒ wf (sub_words ws offset n q k acc)
Proof
  ho_match_mp_tac sub_words_ind \\ rw[]
  \\ rw[Once sub_words_def, wf_put_word]
QED

Theorem lookup_sparse_words:
  ∀kvs acc j.
    lookup j (sparse_words ws offset n kvs acc) =
    if out_word ws offset n j ≠ 0 ∧
       (MEM (offset DIV 32 + j) (MAP FST kvs) ∨
        MEM (offset DIV 32 + j + 1) (MAP FST kvs))
    then SOME (out_word ws offset n j) else lookup j acc
Proof
  Induct >- rw[sparse_words_def]
  \\ Cases \\ rw[sparse_words_def, lookup_put_word] \\ gvs[]
  \\ rw[] \\ gvs[]
QED

Theorem wf_sparse_words:
  ∀kvs acc. wf acc ⇒ wf (sparse_words ws offset n kvs acc)
Proof
  Induct >- rw[sparse_words_def]
  \\ Cases \\ rw[sparse_words_def, wf_put_word]
QED

Theorem out_word_past_end[local]:
  n ≤ 32 * j ⇒ out_word ws offset n j = 0
Proof
  strip_tac \\ ‘n − 32 * j = 0’ by simp[]
  \\ rw[out_word_def, read_word_def]
QED

Theorem div_32_le[local]:
  (m + 31) DIV 32 ≤ j ⇒ m ≤ 32 * j
Proof
  intLib.ARITH_TAC
QED

Theorem lookup_buffer_sub:
  lookup j (buffer_sub offset sz b).words =
  let w = out_word b.words offset (MIN sz (b.len - offset)) j in
  if w ≠ 0 then SOME w else NONE
Proof
  rw[buffer_sub_def, lookup_sub_words, lookup_sparse_words, lookup_def]
  \\ gvs[MEM_MAP, pairTheory.EXISTS_PROD, MEM_toAList]
  >- (drule out_word_nonzero \\ simp[])
  \\ CCONTR_TAC \\ gvs[NOT_LESS]
  \\ drule div_32_le \\ strip_tac
  \\ drule_then assume_tac out_word_past_end \\ gvs[]
QED

Theorem p_split[local]:
  offset + 32 * (p DIV 32) + p MOD 32 = offset + p ∧
  (p MOD 32 < MIN 32 (n − 32 * (p DIV 32)) ⇔ p < n)
Proof
  simp[MIN_DEF] \\ rw[] \\ intLib.ARITH_TAC
QED

Theorem byte_at_buffer_sub:
  byte_at (buffer_sub offset sz b).words p =
  if p < MIN sz (b.len - offset) then byte_at b.words (offset + p) else 0w
Proof
  qabbrev_tac ‘n = MIN sz (b.len - offset)’
  \\ ‘word_at (buffer_sub offset sz b).words (p DIV 32) =
      out_word b.words offset n (p DIV 32)’
       by (simp[word_at_def, lookup_buffer_sub] \\ rw[])
  \\ CONV_TAC (LHS_CONV (REWR_CONV byte_at_def))
  \\ pop_assum SUBST1_TAC
  \\ rewrite_tac[out_word_def]
  \\ DEP_REWRITE_TAC[byte_of_read_word]
  \\ rewrite_tac[p_split]
  \\ simp[]
QED

Theorem good_words_buffer_sub:
  good_words (buffer_sub offset sz b).words
Proof
  rw[good_words_def, lookup_buffer_sub]
  >- rw[buffer_sub_def, wf_sub_words, wf_sparse_words, wf_def]
  \\ simp[word_at_def, lookup_buffer_sub] \\ rw[]
  \\ simp[out_word_def, byte_of_read_word]
QED

Theorem buffer_of_list_take:
  buffer_of_list (buffer_take offset sz b) = buffer_sub offset sz b
Proof
  rw[theorem "buffer_component_equality", buffer_of_list_fields]
  >- simp[buffer_sub_def, buffer_take_def, read_bytes_GENLIST]
  \\ irule good_words_eq
  \\ simp[good_words_buffer_sub, good_words_write_bytes, good_words_LN]
  \\ simp[write_bytes_byte_at, byte_at_LN, byte_at_buffer_sub]
  \\ simp[buffer_take_def, read_bytes_GENLIST, EL_GENLIST]
QED

Theorem buffer_to_list_sub:
  buffer_to_list (buffer_sub offset sz b) =
  TAKE sz (DROP offset (buffer_to_list b))
Proof
  rw[GSYM buffer_of_list_take, buffer_take_to_list]
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
  \\ rpt (pop_assum mp_tac) \\ rw[] \\ gvs[MOD_32_lt];

val () = cv_auto_trans_rec small_bytes_of_num_def
  (cv_measure_tac ‘measure (cv$c2n o FST)’);
val () = cv_auto_trans_rec bytes_of_num_def
  (cv_measure_tac ‘measure (cv$c2n o FST)’);
val () = cv_auto_trans num_of_bytes_def;
val () = cv_auto_trans word_at_def;
val () = cv_auto_trans set_word_def;
val () = cv_auto_trans_rec read_bytes_def
  (cv_measure_tac ‘measure (cv$c2n o FST o SND o SND)’);
val () = cv_auto_trans splice_bytes_def;
val () = cv_auto_trans_rec write_bytes_def
  (cv_measure_tac ‘measure (cv$c2n o FST o SND o SND)’);
val () = cv_auto_trans clear_words_def;
val () = cv_auto_trans zero_bytes_def;
val () = cv_auto_trans read_word_def;
val () = cv_auto_trans out_word_def;
val () = cv_auto_trans put_word_def;
val () = cv_auto_trans sub_words_def;
val () = cv_auto_trans sparse_words_def;
val () = cv_auto_trans size_upto_def;
val () = cv_auto_trans empty_buffer_def;
val () = cv_auto_trans buffer_length_def;
val () = cv_auto_trans buffer_to_list_def;
val () = cv_auto_trans buffer_read_def;
val () = cv_auto_trans buffer_take_def;
val () = cv_auto_trans buffer_sub_def;
val () = cv_auto_trans buffer_extend_def;
val () = cv_auto_trans buffer_write_def;
val () = cv_auto_trans buffer_of_list_def;
