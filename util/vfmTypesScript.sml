open HolKernel boolLib bossLib Parse ParseExtras
     wordsTheory byteTheory numposrepTheory
     finite_mapTheory listTheory combinTheory
     keccakTheory wordsLib blastLib cv_transLib cv_stdTheory;

val _ = new_theory "vfmTypes";

val _ = tight_equality();

(* TODO: figure out what to do with these - proofs too slow? *)

(*
this works but is slow and not needed here - might be needed elsewhere
Theorem set_byte_128:
  set_byte a b (w: 128 word) be =
  let i = byte_index a be in
       if i =   0 then w2w b        || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00w
  else if i =   8 then w2w b <<   8 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFw
  else if i =  16 then w2w b <<  16 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFw
  else if i =  24 then w2w b <<  24 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFw
  else if i =  32 then w2w b <<  32 || w && 0xFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFw
  else if i =  40 then w2w b <<  40 || w && 0xFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFw
  else if i =  48 then w2w b <<  48 || w && 0xFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFw
  else if i =  56 then w2w b <<  56 || w && 0xFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFw
  else if i =  64 then w2w b <<  64 || w && 0xFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFw
  else if i =  72 then w2w b <<  72 || w && 0xFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFw
  else if i =  80 then w2w b <<  80 || w && 0xFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFw
  else if i =  88 then w2w b <<  88 || w && 0xFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFw
  else if i =  96 then w2w b <<  96 || w && 0xFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 104 then w2w b << 104 || w && 0xFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 112 then w2w b << 112 || w && 0xFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else                 w2w b << 120 || w && 0x00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
Proof
  reverse(rw[set_byte_def, word_slice_alt_def])
  >- (
    `byte_index a be = 120`
    by (
      gs[byte_index_def]
      \\ `w2n a MOD 16 < 16` by rw[]
      \\ pop_assum mp_tac
      \\ qmatch_goalsub_abbrev_tac`z < 16 ⇒ f`
      \\ simp_tac std_ss [NUMERAL_LESS_THM]
      \\ strip_tac \\ gs[Abbr`f`]
      \\ rw[] \\ gs[] )
    \\ simp[] \\ BBLAST_TAC)
  \\ BBLAST_TAC
QED
*)

Theorem set_byte_160:
  set_byte a b (w: 160 word) be =
  let i = byte_index a be in
       if i =   0 then w2w b        || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00w
  else if i =   8 then w2w b <<   8 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFw
  else if i =  16 then w2w b <<  16 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFw
  else if i =  24 then w2w b <<  24 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFw
  else if i =  32 then w2w b <<  32 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFw
  else if i =  40 then w2w b <<  40 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFw
  else if i =  48 then w2w b <<  48 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFw
  else if i =  56 then w2w b <<  56 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFw
  else if i =  64 then w2w b <<  64 || w && 0xFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFw
  else if i =  72 then w2w b <<  72 || w && 0xFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFw
  else if i =  80 then w2w b <<  80 || w && 0xFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFw
  else if i =  88 then w2w b <<  88 || w && 0xFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFw
  else if i =  96 then w2w b <<  96 || w && 0xFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 104 then w2w b << 104 || w && 0xFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 112 then w2w b << 112 || w && 0xFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 120 then w2w b << 120 || w && 0xFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 128 then w2w b << 128 || w && 0xFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 136 then w2w b << 136 || w && 0xFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 144 then w2w b << 144 || w && 0xFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else                 w2w b << 152 || w && 0x00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
Proof
  rw_tac std_ss [set_byte_def, word_slice_alt_def]
  \\ reverse(rpt IF_CASES_TAC)
  >- (
    `i = 152`
    by (
      qunabbrev_tac`i`
      \\ full_simp_tac (std_ss ++ boolSimps.LET_ss ++ ARITH_ss) [
            byte_index_def, EVAL``dimindex(:160)``]
      \\ `w2n a MOD 20 < 20` by rw[]
      \\ pop_assum mp_tac
      \\ qmatch_goalsub_abbrev_tac`z < 20 ⇒ f`
      \\ simp_tac std_ss [NUMERAL_LESS_THM]
      \\ strip_tac \\ gs[Abbr`f`]
      \\ rw[] \\ gs[] )
    \\ asm_simp_tac std_ss []
    \\ simp_tac (srw_ss()) []
    \\ BBLAST_TAC)
  \\ asm_simp_tac std_ss []
  \\ simp_tac (srw_ss()) []
  \\ BBLAST_TAC
QED

val () = cv_auto_trans set_byte_160;

val () = cv_auto_trans (INST_TYPE [alpha |-> “:160”] word_of_bytes_def);

Theorem set_byte_256:
  set_byte a b (w: 256 word) be =
  let i = byte_index a be in
       if i =   0 then w2w b        || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00w
  else if i =   8 then w2w b <<   8 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFw
  else if i =  16 then w2w b <<  16 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFw
  else if i =  24 then w2w b <<  24 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFw
  else if i =  32 then w2w b <<  32 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFw
  else if i =  40 then w2w b <<  40 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFw
  else if i =  48 then w2w b <<  48 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFw
  else if i =  56 then w2w b <<  56 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFw
  else if i =  64 then w2w b <<  64 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFw
  else if i =  72 then w2w b <<  72 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFw
  else if i =  80 then w2w b <<  80 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFw
  else if i =  88 then w2w b <<  88 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFw
  else if i =  96 then w2w b <<  96 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 104 then w2w b << 104 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 112 then w2w b << 112 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 120 then w2w b << 120 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 128 then w2w b << 128 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 136 then w2w b << 136 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 144 then w2w b << 144 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 152 then w2w b << 152 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 160 then w2w b << 160 || w && 0xFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 168 then w2w b << 168 || w && 0xFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 176 then w2w b << 176 || w && 0xFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 184 then w2w b << 184 || w && 0xFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 192 then w2w b << 192 || w && 0xFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 200 then w2w b << 200 || w && 0xFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 208 then w2w b << 208 || w && 0xFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 216 then w2w b << 216 || w && 0xFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 224 then w2w b << 224 || w && 0xFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 232 then w2w b << 232 || w && 0xFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 240 then w2w b << 240 || w && 0xFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else                 w2w b << 248 || w && 0x00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
Proof
  rw_tac std_ss [set_byte_def, word_slice_alt_def]
  \\ reverse(rpt IF_CASES_TAC)
  >- (
    `i = 248`
    by (
      qunabbrev_tac`i`
      \\ full_simp_tac (std_ss ++ boolSimps.LET_ss ++ ARITH_ss) [
            byte_index_def, EVAL``dimindex(:256)``]
      \\ `w2n a MOD 32 < 32` by rw[]
      \\ pop_assum mp_tac
      \\ qmatch_goalsub_abbrev_tac`z < 32 ⇒ f`
      \\ simp_tac std_ss [NUMERAL_LESS_THM]
      \\ strip_tac \\ gs[Abbr`f`]
      \\ rw[] \\ gs[] )
    \\ asm_simp_tac std_ss []
    \\ simp_tac (srw_ss()) []
    \\ BBLAST_TAC)
  \\ asm_simp_tac std_ss []
  \\ simp_tac (srw_ss()) []
  \\ BBLAST_TAC
QED

val () = cv_auto_trans set_byte_256;

val () = cv_auto_trans (INST_TYPE [alpha |-> “:256”] word_of_bytes_def);

val () = cv_auto_trans numposrepTheory.n2l_n2lA;

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

Definition num_to_be_bytes_def:
  num_to_be_bytes n : word8 list =
  if n = 0 then [] else REVERSE $ MAP n2w $ n2l 256 n
End

Definition num_of_be_bytes_def:
  num_of_be_bytes bs =
  l2n 256 $ MAP w2n $ REVERSE bs
End

Theorem num_of_to_be_bytes[simp]:
  num_of_be_bytes (num_to_be_bytes n) = n
Proof
  rw[num_of_be_bytes_def, num_to_be_bytes_def, MAP_MAP_o, o_DEF]
  \\ qmatch_goalsub_abbrev_tac`MAP f ls`
  \\ `MAP f ls = MAP I ls`
  by (
    rw[MAP_EQ_f, Abbr`ls`, Abbr`f`]
    \\ qspec_then`256` mp_tac n2l_BOUND
    \\ rw[EVERY_MEM]
    \\ first_x_assum drule \\ rw[] )
  \\ fs[Abbr`ls`]
  \\ irule l2n_n2l
  \\ rw[]
QED

val _ = export_theory();
