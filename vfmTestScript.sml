open HolKernel boolLib bossLib Parse wordsLib
     arithmeticTheory whileTheory
     vfmTypesTheory vfmExecutionTheory
     vfmStateTheory vfmContextTheory
     vfmOperationTheory vfmComputeTheory
     cv_transLib cv_stdTheory cv_computeLib
     cv_primTheory byteTheory;

val _ = new_theory "vfmTest";

(* TODO: move/replace *)
Definition hex_to_bytes_def:
    hex_to_bytes [] = [] : byte list
  ∧ hex_to_bytes [c] = [n2w (UNHEX c)]
  ∧ hex_to_bytes (c1::c2::rest) =
      n2w (16 * UNHEX c1 + UNHEX c2)
      :: hex_to_bytes rest
End

val _ = cv_auto_trans hex_to_bytes_def;

(* cv_eval “hex_to_bytes "693c61390000000000000000000000000000000000000000000000000000000000000000"” *)

Definition empty_accounts_def:
  empty_accounts (a: address) = empty_account_state
End

Theorem build_spt_empty_accounts[simp]:
  ∀n. build_spt empty_account_state n empty_accounts = LN
Proof
  Induct \\ rw[build_spt_def]
  \\ gs[empty_accounts_def]
QED

Theorem empty_accounts_cv_rep[cv_rep]:
  from_evm_accounts empty_accounts = Num 0
Proof
  rw[from_evm_accounts_def, from_sptree_sptree_spt_def]
QED

open dep_rewrite sptreeTheory finite_setTheory listTheory

Theorem from_list_from_word_MAP_w2n:
  from_list from_word l =
  from_list Num (MAP w2n l)
Proof
  Induct_on`l`
  \\ rw[cv_typeTheory.from_list_def, cv_typeTheory.from_word_def]
QED

Theorem fset_ABS_word_cv_rep[cv_rep]:
  from_word_fset (fset_ABS l) =
  cv_list_to_num_set (from_list from_word l)
Proof
  rw[from_word_fset_def, from_num_fset_def,
     from_list_from_word_MAP_w2n,
     GSYM cv_list_to_num_set_thm]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_list_to_num_set, lookup_list_to_num_set, MEM_fset_REP]
  \\ simp[GSYM fromSet_set, IN_fromSet, MEM_MAP]
  \\ metis_tac[]
QED

Theorem fIMAGE_fUNION:
  fIMAGE f (fUNION s1 s2) =
  fUNION (fIMAGE f s1) (fIMAGE f s2)
Proof
  rw[finite_setTheory.EXTENSION, EQ_IMP_THM]
  \\ metis_tac[]
QED

Theorem fUNION_storage_key_cv_rep[cv_rep]:
  from_storage_key_fset (fUNION s1 s2) =
  cv_union (from_storage_key_fset s1) (from_storage_key_fset s2)
Proof
  rw[from_storage_key_fset_def, fIMAGE_fUNION, fUNION_num_cv_rep]
QED

Theorem fEMPTY_storage_key_cv_rep[cv_rep]:
  from_storage_key_fset fEMPTY = Num 0
Proof
  rw[from_storage_key_fset_def, fEMPTY_num_cv_rep]
QED

Theorem toSet_fset_ABS:
  !l. toSet (fset_ABS l) = set l
Proof
  gen_tac \\
  qspec_then`l`(SUBST1_TAC o SYM o Q.AP_TERM`toSet`)fromSet_set
  \\ irule toSet_fromSet
  \\ rw[]
QED

Theorem toSet_fUNION[simp]:
  toSet (fUNION s1 s2) = (toSet s1) UNION (toSet s2)
Proof
  rw[pred_setTheory.EXTENSION, GSYM fIN_IN]
QED

Theorem fset_ABS_MAP:
  fset_ABS (MAP f l) = fIMAGE f (fset_ABS l)
Proof
  rw[finite_setTheory.EXTENSION, fIN_IN, toSet_fset_ABS, MEM_MAP]
  \\ metis_tac[]
QED

Theorem fset_REP_fEMPTY[simp]:
  fset_REP fEMPTY = []
Proof
  rw[rich_listTheory.NIL_NO_MEM, MEM_fset_REP]
QED

Theorem fIN_fset_ABS:
  fIN x (fset_ABS l) <=> MEM x l
Proof
  rw[fIN_def]
  \\ mp_tac fset_QUOTIENT
  \\ rewrite_tac[quotientTheory.QUOTIENT_def,fsequiv_def]
  \\ rpt strip_tac
  \\ `set (fset_REP (fset_ABS l)) = set l`
  suffices_by (
    rewrite_tac[pred_setTheory.EXTENSION]
    \\ metis_tac[] )
  \\ asm_simp_tac std_ss []
QED

Theorem fBIGUNION_fset_ABS_FOLDL_aux[local]:
  !l s. FOLDL fUNION s l = fUNION s (fBIGUNION (fset_ABS l))
Proof
  Induct \\ rw[fBIGUNION_def, GSYM fEMPTY_def]
  \\ rw[GSYM fUNION_ASSOC] \\ AP_TERM_TAC
  \\ rw[finite_setTheory.EXTENSION]
  \\ qmatch_goalsub_abbrev_tac`_ \/ fIN e s <=> fIN e hs`
  \\ `hs = fUNION h s`
  by (
    rw[Once (GSYM toSet_11)]
    \\ rw[Abbr`hs`, Abbr`s`, toSet_fset_ABS]
    \\ rw[pred_setTheory.EXTENSION, MEM_FLAT, PULL_EXISTS, MEM_MAP]
    \\ rw[MEM_fset_REP, fIN_fset_ABS, GSYM fIN_IN]
    \\ metis_tac[] )
  \\ rw[]
QED

Theorem fBIGUNION_fset_ABS_FOLDL:
  fBIGUNION (fset_ABS l) = FOLDL fUNION fEMPTY l
Proof
  rw[fBIGUNION_fset_ABS_FOLDL_aux]
QED

Theorem fIMAGE_MAP:
  fIMAGE f s = fset_ABS (MAP f (fset_REP s))
Proof
  rw[finite_setTheory.EXTENSION, fIN_fset_ABS, MEM_MAP, MEM_fset_REP]
  \\ metis_tac[]
QED

(* TODO: does this already exist? *)
Definition domain_list_def:
  domain_list LN = [] ∧
  domain_list (LS _) = [0n] ∧
  domain_list (BN t1 t2) =
     MAP (λn. 2 * n + 2) (domain_list t1) ++
     MAP (λn. 2 * n + 1) (domain_list t2) ∧
  domain_list (BS t1 v t2) =
     0::
     MAP (λn. 2 * n + 2) (domain_list t1) ++
     MAP (λn. 2 * n + 1) (domain_list t2)
End

val () = cv_auto_trans domain_list_def;

val cv_domain_list_thm = theorem"cv_domain_list_thm";

Theorem set_domain_list:
  set (domain_list t) = domain t
Proof
  Induct_on`t` \\ rw[domain_list_def, LIST_TO_SET_MAP]
  \\ rw[pred_setTheory.EXTENSION] \\ metis_tac[]
QED

Definition MAP_word_join_num_def:
  MAP_word_join_num x ls =
  MAP (w2n : (256 + 160) word -> num o flip word_join x o n2w) ls
End

val () = MAP_word_join_num_def |> SIMP_RULE std_ss [combinTheory.C_DEF] |> cv_auto_trans;
val cv_MAP_word_join_num_thm = theorem "cv_MAP_word_join_num_thm";

Theorem from_storage_key_fset_fIMAGE_SK_cv_rep[cv_rep]:
  from_storage_key_fset (fIMAGE (SK x) s) =
  cv_list_to_num_set $
    cv_MAP_word_join_num (from_word x) (cv_domain_list (from_word_fset s))
Proof
  rw[from_storage_key_fset_def, from_num_fset_def,
     from_word_fset_def, GSYM cv_domain_list_thm,
     GSYM cv_MAP_word_join_num_thm,
     GSYM cv_list_to_num_set_thm]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_list_to_num_set, lookup_list_to_num_set,
          MEM_fset_REP, MAP_word_join_num_def, MEM_MAP,
          set_domain_list, domain_list_to_num_set, PULL_EXISTS]
  \\ metis_tac[]
QED

val () = initial_access_sets_def
 |> SIMP_RULE std_ss [
      GSYM fset_ABS_MAP,
      fBIGUNION_fset_ABS_FOLDL
    ]
 |> cv_auto_trans;

val () = cv_auto_trans initial_tx_params_def;

val () = initial_state_def |>
  ONCE_REWRITE_RULE[GSYM lookup_account_def] |>
  ONCE_REWRITE_RULE[GSYM update_account_def] |>
  ONCE_REWRITE_RULE[GSYM update_account_def] |>
  cv_auto_trans;

(*
https://github.com/ethereum/tests
commit 08839f5 (taken from the develop branch)
BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json
*)

Definition add_d0g0v0_Cancun_block_def:
  add_d0g0v0_Cancun_block =
  <| number := 0x01
   ; baseFee := 0x0a
   ; timeStamp := 0x03e8
   ; coinBase := n2w 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba
   ; gasLimit := 0x05f5e100
   ; prevRandao := n2w 0x00 (* not sure - using the difficulty *)
  |>
End

Definition add_d0g0v0_Cancun_transaction_def:
  add_d0g0v0_Cancun_transaction =
  <| from := n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b
   ; to   := n2w 0xcccccccccccccccccccccccccccccccccccccccc
   ; data := hex_to_bytes $ CONCAT [
               "693c61390000000000000000000000000000";
               "000000000000000000000000000000000000" ]
   ; nonce := 0x00
   ; value := 0x01
   ; gasPrice := 0x0a
   ; gasLimit := 0x04c4b400
   ; accessList := []
   |>
End

Definition add_d0g0v0_Cancun_pre_def:
  add_d0g0v0_Cancun_pre =
  update_account (
  update_account (
  update_account (
  update_account (
  update_account (
  update_account (
  update_account empty_accounts
    (n2w 0x0000000000000000000000000000000000001000)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["7ffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffffffffffffffff7fffffffffff"
                 ;"fffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001001)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60047fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001002)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60017fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001003)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes "600060000160005500"
     |>
  )
    (n2w 0x0000000000000000000000000000000000001004)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                  ["7fffffffffffffffffffffffffffffffffffffff"
                  ;"ffffffffffffffffffffffffff60010160005500"]
     |>
  )
    (n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := []
     |>
  )
    (n2w 0xcccccccccccccccccccccccccccccccccccccccc)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes "600060006000600060006004356110000162fffffff100"
     |>
End

Definition add_d0g0v0_Cancun_post_def:
  add_d0g0v0_Cancun_post =
  update_account (
  update_account (
  update_account (
  update_account (
  update_account (
  update_account (
  update_account empty_accounts
    (n2w 0x0000000000000000000000000000000000001000)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := (n2w 0x00 =+ n2w 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe) empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["7ffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffffffffffffffff7fffffffffff"
                 ;"fffffffffffffffffffffffffffffffffffffff"
                 ;"fffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001001)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60047fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001002)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                 ["60017fffffffffffffffffffffffffffffffffff"
                 ;"ffffffffffffffffffffffffffffff0160005500"]
     |>
  )
    (n2w 0x0000000000000000000000000000000000001003)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes "600060000160005500"
     |>
  )
    (n2w 0x0000000000000000000000000000000000001004)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9ce
     ; storage := empty_storage
     ; code := hex_to_bytes $ CONCAT
                  ["7fffffffffffffffffffffffffffffffffffffff"
                  ;"ffffffffffffffffffffffffff60010160005500"]
     |>
  )
    (n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b)
    <| nonce := 0x01
     ; balance := 0x0ba1a9ce0b9aa781
     ; storage := empty_storage
     ; code := []
     |>
  )
    (n2w 0xcccccccccccccccccccccccccccccccccccccccc)
    <| nonce := 0x00
     ; balance := 0x0ba1a9ce0ba1a9cf
     ; storage := empty_storage
     ; code := hex_to_bytes "600060006000600060006004356110000162fffffff100"
     |>
End

Theorem add_d0g0v0_Cancun_pre_code:
  (add_d0g0v0_Cancun_pre add_d0g0v0_Cancun_transaction.to).code =
  hex_to_bytes "600060006000600060006004356110000162fffffff100"
Proof
  simp[add_d0g0v0_Cancun_pre_def, add_d0g0v0_Cancun_transaction_def,
       update_account_def]
QED

fun cv_eval_match_tac pat =
  goal_term (fn tm =>
               let
                 val t = find_term (can (match_term pat)) tm
               in rewrite_tac [cv_eval t] end);

fun eval_match_tac pat =
  goal_term (fn tm =>
               let
                 val t = find_term (can (match_term pat)) tm
               in rewrite_tac [EVAL t] end);

val () = mk_word_size 256;

val () = cv_auto_trans add_d0g0v0_Cancun_pre_def;
val () = add_d0g0v0_Cancun_post_def |>
  ONCE_REWRITE_RULE[GSYM update_storage_def] |>
  cv_auto_trans;
val () = cv_auto_trans add_d0g0v0_Cancun_transaction_def;
val () = cv_auto_trans add_d0g0v0_Cancun_block_def;

Definition run_with_fuel_def:
  run_with_fuel n (r, s) =
  if ISR r then SOME (OUTR r, s, n)
  else case n of
  | 0 => NONE
  | SUC m => run_with_fuel m (step s)
End

val run_with_fuel_pre_def = cv_auto_trans_pre run_with_fuel_def;

val run_with_fuel_ind = theorem"run_with_fuel_ind";

Theorem run_with_fuel_pre[cv_pre]:
  ∀n v. run_with_fuel_pre n v
Proof
  simp[pairTheory.FORALL_PROD]
  \\ ho_match_mp_tac run_with_fuel_ind
  \\ rpt strip_tac
  \\ rw[Once run_with_fuel_pre_def]
QED

Definition run_n_def:
  run_n n s = FUNPOW (step o SND) n (INL (), s)
End

val () = cv_auto_trans run_n_def;

val WHILE_FUNPOW = keccakTheory.WHILE_FUNPOW

Theorem run_SOME_run_n:
  run s = SOME z ⇔
  (∃n t. run_n n s = (INR z, t) ∧
         ∀m. m < n ⇒ ISL (FST (run_n m s)))
Proof
  rw[run_def, run_n_def, EQ_IMP_THM]
  >- (
    imp_res_tac OWHILE_WHILE
    \\ imp_res_tac OWHILE_ENDCOND
    \\ qmatch_assum_rename_tac `~_ p`
    \\ Cases_on`p` \\ gs[]
    \\ qexists_tac`LEAST n. ~(ISL o FST) (FUNPOW (step o SND) n (INL (), s))`
    \\ DEP_REWRITE_TAC[GSYM WHILE_FUNPOW]
    \\ gs[combinTheory.o_DEF]
    \\ numLib.LEAST_ELIM_TAC \\ gs[]
    \\ conj_asm1_tac
    >- (
      spose_not_then strip_assume_tac
      \\ qmatch_assum_abbrev_tac `OWHILE G f z = _`
      \\ `∀n. G (FUNPOW f n z)` by  (
        rw[Abbr`G`] \\ gs[sumTheory.NOT_ISR_ISL] )
      \\ imp_res_tac OWHILE_EQ_NONE
      \\ gs[] )
    \\ rw[] )
  \\ simp[OWHILE_def]
  \\ conj_asm1_tac >- ( qexists_tac`n` \\ gs[] )
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- metis_tac[]
  \\ rw[]
  \\ qmatch_goalsub_rename_tac`FUNPOW _ m`
  \\ Cases_on`m < n` >- metis_tac[sumTheory.NOT_ISR_ISL]
  \\ Cases_on`n < m` >- metis_tac[SIMP_CONV std_ss [] ``ISL (INR _)``, pairTheory.FST]
  \\ `n = m` by gs[]
  \\ gs[]
QED

Theorem run_with_fuel_to_zero_aux[local]:
  ∀n x s z t m.
    run_with_fuel n (x, s) = SOME (z, t, m) ∧
    ISL (FST (x, s)) ∧ m = 0 ⇒
    run_n n (SND (x, s)) = (INR z, t) ∧
    (∀l. l < n ⇒ ISL (FST (run_n l (SND (x, s)))))
Proof
  ho_match_mp_tac run_with_fuel_ind
  \\ gs[]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ qhdtm_x_assum`run_with_fuel`mp_tac
  \\ simp[Once run_with_fuel_def]
  \\ Cases_on`r` \\ gs[]
  \\ gs[num_case_eq, run_n_def]
  \\ disch_then strip_assume_tac
  \\ gvs[]
  \\ simp[Once FUNPOW]
  \\ Cases_on`step s` \\ gs[]
  \\ qmatch_assum_rename_tac`step s = (x,y)`
  \\ Cases_on`x` \\ gs[]
  >- ( Cases \\ simp[Once FUNPOW] )
  \\ qhdtm_x_assum`run_with_fuel`mp_tac
  \\ rw[Once run_with_fuel_def]
QED

Theorem run_with_fuel_to_zero:
  run_with_fuel n (INL (), s) = SOME (z, t, 0) ⇒
  run_n n s = (INR z, t) ∧
  (∀m. m < n ⇒ ISL (FST (run_n m s)))
Proof
  strip_tac
  \\ drule run_with_fuel_to_zero_aux
  \\ gs[]
QED

(*

cv_eval ``
  (HD (SND (run_n 16 (initial_state 1
    add_d0g0v0_Cancun_pre
    add_d0g0v0_Cancun_block
    (Memory <| offset := 0; size := 0 |>)
    add_d0g0v0_Cancun_transaction))).contexts).stack
``

cv_eval ``
  (EL 0 (SND (run_n 11 (initial_state 1
    add_d0g0v0_Cancun_pre
    add_d0g0v0_Cancun_block
    (Memory <| offset := 0; size := 0 |>)
    add_d0g0v0_Cancun_transaction))).contexts).pc
``

initial_context_def

val callee_code = cv_eval ``
  (HD (SND (run_n 12 (initial_state 1
    add_d0g0v0_Cancun_pre
    add_d0g0v0_Cancun_block
    (Memory <| offset := 0; size := 0 |>)
    add_d0g0v0_Cancun_transaction))).contexts).callParams.code
`` |> concl |> rand |> rhs

cv_eval ``parse_opcode (DROP 0 ^callee_code)``
Push32 -1
Push32 -1
Add
Push1 0
SStore
Stop

TypeBase.fields_of``:transaction_state`` |> map fst
TypeBase.fields_of``:context`` |> map fst
TypeBase.fields_of``:call_parameters`` |> map fst

cv_eval ``parse_opcode (DROP 21 ^(rhs(concl add_d0g0v0_Cancun_pre_code)))``
Push1 0
Push1 0
Push1 0
Push1 0
Push1 0
Push1 4
CallDataLoad
Push2 16 0
Add
Push3 255 255 255
Call
Stop
*)

open cv_typeTheory cvTheory

Definition refund_gas_def:
  refund_gas (sender: address) refund accounts : evm_accounts =
  (sender =+ accounts sender with balance updated_by $+ refund) accounts
End

val () = refund_gas_def |>
  ONCE_REWRITE_RULE[GSYM lookup_account_def] |>
  ONCE_REWRITE_RULE[GSYM update_account_def] |>
  cv_auto_trans;

(*
Theorem add_d0g0v0_Cancun_correctness:
  ∃s r.
    initial_state 1
      add_d0g0v0_Cancun_pre
      add_d0g0v0_Cancun_block
      (Memory <| offset := 0; size := 0 |>)
      add_d0g0v0_Cancun_transaction = SOME s ∧
    run s = SOME (Finished r) ∧
    refund_gas add_d0g0v0_Cancun_transaction.from
      r.refund r.accounts = add_d0g0v0_Cancun_post
Proof
  rw[run_SOME_run_n, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`SOME _ = s`
  \\ `s <> NONE`
   by ( qunabbrev_tac`s` \\ cv_eval_match_tac``_``)
  \\ `∃n z t.
        run_with_fuel n (INL (), THE s) = SOME (Finished z, t, 0) ∧
        refund_gas
          add_d0g0v0_Cancun_transaction.from z.refund
          z.accounts = add_d0g0v0_Cancun_post`
      suffices_by (
    strip_tac
    \\ Cases_on`s` \\ gs[]
    \\ drule run_with_fuel_to_zero
    \\ strip_tac
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gs[] )
  \\ qunabbrev_tac`s`
  \\ qmatch_asmsub_abbrev_tac`Memory m`
  \\ `m = memory_range 0 0` by (rw[Abbr`m`] \\ cv_eval_match_tac``_``)
  \\ fs[Abbr`m`]
  \\ qexists_tac`18`
  \\ (fn goal as (_, gt) =>
    let
      val run_tm = find_term (can (match_term ``run_with_fuel _ _``)) gt
      val raw_th = cv_eval_raw run_tm
      val raw_th2 = raw_th |>
      REWRITE_RULE[
        cv_typeTheory.to_option_def,
        cv_typeTheory.to_pair_def,
        to_vfmExecution_outcome_def,
        cv_typeTheory.cv_has_shape_def,
        cvTheory.Num_11,
        EVAL``2n = 0``,
        EVAL``2n = 1``,
        EVAL``1n = 0``,
        to_vfmExecution_result_def,
        to_evm_accounts_def,
        cv_typeTheory.to_list_def,
        cvTheory.cv_fst_def,
        cvTheory.cv_snd_def,
        cvTheory.c2n_def,
        to_vfmContext_transaction_state_def,
        to_vfmContext_transaction_parameters_def,
        to_vfmContext_access_sets_def,
        to_vfmContext_context_def,
        to_vfmContext_call_parameters_def,
        to_vfmContext_return_destination_def,
        to_vfmContext_memory_range_def,
        to_evm_accounts_def,
        to_num_fset_def,
        to_word_fset_def,
        to_storage_key_fset_def,
        to_word_def,
        to_option_def,
        cv_has_shape_def,
        c2n_def, c2b_thm,
        to_list_def, cv_fst_def, cv_snd_def
      ]
    in
      rewrite_tac[UNDISCH raw_th2]
    end goal)
  \\ simp[] \\ EVAL_TAC
  \\ rw[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- gs[account_state_component_equality, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
  \\ rw[]

  Globals.max_print_depth := 12

val ts_tm = raw_th2 |> concl |> rhs |> rand |> rand

ts_tm |>
REWRITE_CONV[
  to_vfmContext_transaction_state_def,
  to_vfmContext_transaction_parameters_def,
  to_vfmContext_access_sets_def,
  to_vfmContext_context_def,
  to_vfmContext_call_parameters_def,
  to_vfmContext_return_destination_def,
  to_vfmContext_memory_range_def,
  to_evm_accounts_def,
  to_num_fset_def,
  to_word_fset_def,
  to_storage_key_fset_def,
  to_word_def,
  to_option_def,
  cv_has_shape_def,
  c2n_def, c2b_thm,
  to_list_def, cv_fst_def, cv_snd_def
]
          |> concl |> rhs

val to_sptree_spt_cs = computeLib.bool_compset();
val () = computeLib.add_thms [
  to_sptree_spt_def,
  cv_has_shape_def,
  cv_snd_def,
  cv_fst_def
] to_sptree_spt_cs;

val spt_tm = raw_th2 |> concl |>
  find_term (can (match_term ``to_sptree_spt _ _``))

rawterm_pp (fn () => (concl (EVAL spt_tm))) ()
val probtm = rhs(concl(EVAL spt_tm))
el 3 (snd (strip_comb probtm))
term_size probtm

computeLib.CBV_CONV to_sptree_spt_cs spt_tm
spt_tm |> term_size
PolyML.Exception.traceException((fn () =>
  term_to_string (concl (EVAL spt_tm))),(fn (ss,e) => String.concat(ss)))
(term_to_string (concl (EVAL spt_tm)); NONE)
handle e => PolyML.Exception.exceptionLocation e
showSig"Parse"
(if aconv (concl (EVAL spt_tm)) T then SOME {endLine=0, endPosition=0, file="done", startLine=0,
startPosition=0} else NONE) handle e => PolyML.Exception.exceptionLocation e

showStruct"PolyML"

showSig"INTEGER"
Int.maxInt

m``Num _ = Num _``
f"cv_has_shape"
Globals.max_print_depth := 13;
Globals.max_print_depth := ~1;

  add_d0g0v0_Cancun_pre_code

  \\_t DEP_REWRITE_TAC[run_with_fuel_to_zero]
  rw[run_def, Once OWHILE_THM, PULL_EXISTS]
  \\ cv_eval_match_tac ``step _``
  \\ rw[Once OWHILE_THM]
  \\ cv_eval_match_tac ``step _``

  \\ cv_eval_match_tac ``(Memory _)``
  \\ cv_eval_match_tac ``(initial_state _ _ _ _ _)``
  initial_state_def
  cv_in
  ff"initial_state""cv"
  step_def

  \\ rw[step_def]
  \\ rw[Once bind_def]
  \\ eval_match_tac “get_current_context _”
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac ‘pair_CASE (_ _ ctx) body’
  \\ cv_eval_match_tac ``parse_opcode _`` \\ rw[]
  \\ rw[bind_def, ignore_bind_def, assert_def]
  \\ cv_eval_match_tac ``step_inst _``

  initial_state_def
  type_of``c.outputTo``
  TypeBase.fields_of``:memory_range`` |> map type_of
  type_of``Memory``
  initial_tx_params_def
  \\ cv_eval_match_tac ``step _``

  rpt (
    rw[run_def, Once OWHILE_THM, step_def]
    (* context *)
    \\rw[Once bind_def]
    \\ eval_match_tac “get_current_context _”
    \\rw[]

    \\qmatch_goalsub_abbrev_tac ‘pair_CASE (_ _ ctx) body’

    (* assert T *)
    \\rw[Once ignore_bind_def, Once bind_def, assert_def]
    \\cv_eval_match_tac “parse_opcode _”
    \\rw[]

    \\rw[Once ignore_bind_def, Once bind_def, consume_gas_def]
    \\rw[Once bind_def]
    \\eval_match_tac “get_current_context _”
    \\qunabbrev_tac ‘ctx’

    \\rw[Once ignore_bind_def, Once bind_def, assert_def]
    \\rw[Once ignore_bind_def, Once bind_def, set_current_context_def, return_def]
    \\rw[Once ignore_bind_def, Once bind_def, step_inst_def]
    \\eval_match_tac “get_current_context _”
    \\rw[]
    (* assert T *)
    \\rw[Once ignore_bind_def, Once bind_def, assert_def]
    \\rw[Once ignore_bind_def, Once bind_def, set_current_context_def, return_def]
    (* inc_pair *)
    \\rw[inc_pc_def]
    \\rw[Once bind_def]
    \\eval_match_tac “get_current_context _”
    \\ rw[]
    \\rw[Once ignore_bind_def, Once bind_def, set_current_context_def, return_def]

    \\unabbrev_all_tac
    \\rw[]
    )
  \\ rpt
     (
     rw[Once OWHILE_THM, step_def]
     \\qmatch_goalsub_abbrev_tac ‘pair_CASE (_ _ _) body’

     \\rw[Once bind_def]
     \\eval_match_tac “get_current_context _”
     \\rw[]
     (* assert T *)
     \\rw[Once ignore_bind_def, Once bind_def, assert_def]
     \\cv_eval_match_tac “parse_opcode _”
     \\rw[]
     (* consume gas *)
     \\rw[Once ignore_bind_def, Once bind_def, consume_gas_def]
     \\rw[Once bind_def]
     \\eval_match_tac “get_current_context _”
     \\rw[]
     (* assert T *)
     \\rw[Once ignore_bind_def, Once bind_def, assert_def]
     \\rw[set_current_context_def, return_def]

     (* step_inst *)
     \\rw[Once ignore_bind_def, Once bind_def]
     \\rw[step_inst_def]
     \\rw[binop_def, stack_op_def]
     \\rw[Once bind_def, step_inst_def]
     \\eval_match_tac “get_current_context _”
     \\rw[]
     (* assert T *)
     \\rw[Once ignore_bind_def, Once bind_def, assert_def]
     \\rw[set_current_context_def, return_def]

     \\rw[inc_pc_def, opcode_def]
     \\rw[Once bind_def]
     \\eval_match_tac “get_current_context _”
     \\rw[]
     \\rw[set_current_context_def, return_def]
     \\unabbrev_all_tac
     \\ rw[]
     )

  \\rw[set_byte_0ws]
  \\rw[Once OWHILE_THM, step_def]
  \\rw[Once bind_def]
  \\eval_match_tac “get_current_context _”
  \\rw[]
  (* assert T *)
  \\rw[Once ignore_bind_def, Once bind_def, assert_simps]
  (* parse opcode *)
  \\cv_eval_match_tac “parse_opcode _”
  \\rw[]

   (* CONSUME GAS *)
  \\rw[Once ignore_bind_def, Once bind_def, consume_gas_def]
  \\rw[Once bind_def]
  \\eval_match_tac “get_current_context _”
  \\rw[]
  (* assert T *)
  \\rw[Once ignore_bind_def, Once bind_def, assert_def]
  \\rw[set_current_context_def, return_def]

  \\rw[Once ignore_bind_def, Once bind_def]
  \\rw[step_inst_def]
  \\rw[Once bind_def]
  \\eval_match_tac “get_current_context _”
  \\rw[]
      (* assert T *)
  \\rw[Once ignore_bind_def, Once bind_def, assert_simps]
  \\rw[Once bind_def, access_address_def]
  (* return *)
  \\rw[return_def]
(* get accounts *)
  \\rw[Once bind_def, get_accounts_def]
  \\rw[return_def]
  \\rw[Once ignore_bind_def, Once bind_def, memory_expansion_cost_def]
  \\rw[memory_cost_def]
  \\ ‘word_size 0 = 0’ by rw[word_size_def]
  \\rw[]
  \\rw[bitstringTheory.length_pad_right]
      (* consume gas *)
  \\rw[Once ignore_bind_def, Once bind_def, consume_gas_def]
  \\eval_match_tac “get_current_context _”
  \\rw[]
  \\rw[Once bind_def, assert_simps]
  \\rw[set_current_context_def, return_def]
      (* assert T *)
  \\rw[Once ignore_bind_def, Once bind_def, assert_simps]
  \\rw[Once ignore_bind_def, Once bind_def]
  \\rw[Once bind_def]
  \\eval_match_tac “get_current_context _”
  \\rw[]

  \\ cheat
QED
Globals.max_print_depth := ~1;
*)

(*
Definition CrashingTransaction_transaction_def:
  CrashingTransaction_transaction =
  <| from     := n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b
   ; to       := n2w 0x0
   ; data     := hex_to_bytes $ CONCAT
                 ["60606040525b5b61c3505a1115602c57604051603480"
                 ;"6039833901809050604051809103906000f050600656"
                 ;"5b5b600a80606d6000396000f360606040525b3373ff"
                 ;"ffffffffffffffffffffffffffffffffffffff16ff5b"
                 ;"600a80602a6000396000f360606040526008565b0060"
                 ;"606040526008565b00"]
   ; nonce    := 0x0cc6
   ; value    := 0x01
   ; gasLimit := 0x47127a
   ; gasPrice := 0x0b
   ; accessList := []
   |>
End
secretKey = 0x45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8

Definition CrashingTransaction_pre_def:
  CrashingTransaction_pre accounts ⇔
  let account = accounts (n2w 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b) in
    account.balance = 0x0de0b6b3a7640000 ∧
    account.code = [] ∧
    account.nonce = 0x0cc6 ∧
    account.storage = K 0w
End

(*
Definition CrashingTransaction_post_def:
  CrashingTransaction_post r ⇔
    state hash = n2w 0x7f2928f3c2a99e47eedce1880f49dbf3c44f9d304ec80bb7a14d755fae19a518
    logs hash = n2w 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347

                    "txbytes" : "0xf8c6820cc60b8347127a8001b87760606040525b5b61c3505a1115602c576040516034806039833901809050604051809103906000f0506006565b5b600a80606d6000396000f360606040525b3373ffffffffffffffffffffffffffffffffffffffff16ff5b600a80602a6000396000f360606040526008565b0060606040526008565b001ba0e3ff099a5b59f34c2e88fd6a42e44bf6ae186ebd06fa62aa18044da6a6d98df3a03efe897c69df0d45e18dd61580de2b700952cc9bc794fe05d0c6bf5e7f63d1d1"
*)
*)

val _ = export_theory();
