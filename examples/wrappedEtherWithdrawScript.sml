(* WETH's withdraw(uint256), from the block summaries of
   wrappedEtherTheory composed along its paths, through the CALL that
   pays the caller, and lifted to run_transaction. *)
Theory wrappedEtherWithdraw
Ancestors
  arithmetic list rich_list combin pair pred_set byte cv_std words
  vfmTypes vfmConstants vfmState vfmContext vfmExecution vfmExecutionProp
  vfmBuffer
  set_sep prog vfmProg vfmProgCall contractABI wrappedEther wrappedEtherName
  wrappedEtherTransfer wrappedEtherDeposit
Libs
  dep_rewrite wordsLib cv_transLib evmDecompLib wrappedEtherPathLib

(* ---------------------------------------------------------------- *)
(* The abstract withdrawal *)

Definition WETH_withdraw_def:
  WETH_withdraw a n ws =
  ws with <| balances updated_by (a =+ ws.balances a - n)
           ; locked updated_by (λl. l - n) |>
End

Theorem wf_WETH_withdraw:
  wf_WETH_state ws ∧ n ≤ ws.balances a ⇒ wf_WETH_state (WETH_withdraw a n ws)
Proof
  rw[wf_WETH_state_def, WETH_withdraw_def, SUBSET_DEF, APPLY_UPDATE_THM]
  >- (qpat_x_assum `∀x. 0 < ws.balances x ⇒ _` irule
      \\ Cases_on `a = x` \\ gvs[])
  >- (qpat_x_assum `∀a. ws.balances a < _` (qspec_then `a'` mp_tac)
      \\ rw[])
  \\ gvs[total_balances_def]
  \\ Cases_on `n = 0` >- gvs[APPLY_UPDATE_ID]
  \\ `a ∈ ws.touched`
     by (qpat_x_assum `∀x. 0 < ws.balances x ⇒ _` irule \\ simp[])
  \\ qpat_x_assum `SIGMA _ _ ≤ _` mp_tac
  \\ drule_then (SUBST1_TAC o SYM) INSERT_DELETE
  \\ simp[SUM_IMAGE_INSERT, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac `s1 + _ ≤ _ ⇒ s2 + _ ≤ _`
  \\ `s1 = s2` suffices_by rw[]
  \\ simp[Abbr`s1`, Abbr`s2`]
  \\ irule SUM_IMAGE_CONG
  \\ rw[APPLY_UPDATE_THM]
QED

(* ---------------------------------------------------------------- *)
(* Calldata starting with withdraw(uint256)'s selector *)

Theorem withdraw_selector_eq:
  function_selector "withdraw" [Uint 256] = [0x2Ew; 0x1Aw; 0x7Dw; 0x4Dw]
Proof
  CONV_TAC (LAND_CONV cv_eval) \\ rw[]
QED

Theorem withdraw_selector_calldata:
  0xFFFFFFFFw &&
  word_of_bytes F 0w
    (REVERSE (take_pad_0 32 ([0x2Ew; 0x1Aw; 0x7Dw; 0x4Dw] ++ rest))) //
  (0x100000000000000000000000000000000000000000000000000000000w : bytes32)
  = 0x2E1A7D4Dw
Proof
  qabbrev_tac `sel = [0x2Ew; 0x1Aw; 0x7Dw; 0x4Dw] : word8 list`
  \\ `∃r. take_pad_0 32 (sel ++ rest) = sel ++ r ∧ LENGTH r = 28`
  by rw[take_pad_0_def, TAKE_APPEND, PAD_RIGHT, Abbr`sel`, LENGTH_TAKE_EQ]
  \\ simp[GSYM word_of_bytes_le_def]
  \\ DEP_REWRITE_TAC[word_of_bytes_le_eq_num_of_bytes]
  \\ simp[REVERSE_APPEND, num_of_bytes_APPEND, word_div_def]
  \\ qspec_then `REVERSE r` assume_tac num_of_bytes_lt
  \\ `num_of_bytes (REVERSE sel) = 0x2E1A7D4D`
  by simp[Abbr`sel`, num_of_bytes_def, dimword_8]
  \\ gvs[]
  \\ `num_of_bytes (REVERSE r) + 256 ** 28 * 0x2E1A7D4D < dimword (:256)`
  by simp[]
  \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ qmatch_goalsub_abbrev_tac `(a + b) DIV c`
  \\ `a < c` by simp[Abbr`a`, Abbr`c`]
  \\ `(a + b) DIV c = 773487949`
  by (`a + b = 773487949 * c + a` by simp[Abbr`b`, Abbr`c`]
      \\ pop_assum SUBST1_TAC
      \\ simp[ADD_DIV_ADD_DIV, LESS_DIV_EQ_ZERO, Abbr`c`])
  \\ simp[]
QED

Theorem withdraw_value_enc[local]:
  enc (Tuple [Uint 256]) (ListV [NumV wad]) = word_to_bytes (n2w wad : bytes32) T
Proof
  simp[head_lengths_def, REV_DEF]
QED

(* ---------------------------------------------------------------- *)
(* Composing through the CALL

   The CALL paying the caller is SPEC_Call_stipend, whose post is
   existential in the callee's outcome (success, its output, the gas it
   leaves, its logs and refunds, the rollback state after it), all bound by
   one condition K. compose_blocks and compose_region need fixed
   resources, so the rule is instantiated at the state the path reaches,
   both framed, and composed by hand; the code after the CALL is composed
   for any outcome and put under the existentials. *)

fun spec_parts th =
  case strip_comb (concl th) of
    (_, [m, p, c, q]) => (m, p, c, q)
  | _ => raise mk_HOL_ERR "wrappedEtherWithdraw" "spec_parts" ""

fun head_name tm =
  let val f = fst (strip_comb tm) in
    if is_const f then fst (dest_const f) else ""
  end

fun mk_stars star (x :: xs) =
      List.foldl (fn (f, acc) => list_mk_comb (star, [acc, f])) x xs
  | mk_stars _ [] = raise mk_HOL_ERR "wrappedEtherWithdraw" "mk_stars" ""

val star_eq_conv = SIMP_CONV bool_ss [AC STAR_ASSOC STAR_COMM]

(* removes hypotheses v = t, and t = (v1, v2), by instantiating the
   variables, except those in keep *)
fun elim_defs keep th =
  let
    fun try th h =
      let val (l, r) = dest_eq h in
        if is_var l andalso not (tmem l keep) andalso not (free_in l r) then
          SOME (PROVE_HYP (REFL r) (INST [l |-> r] th))
        else if pairSyntax.is_pair r andalso
                List.all (fn v => is_var v andalso not (tmem v keep))
                         (pairSyntax.strip_pair r) andalso
                not (List.exists (fn v => free_in v l)
                                 (pairSyntax.strip_pair r)) then
          let val (v1, v2) = pairSyntax.dest_pair r
              val th' = INST [v1 |-> pairSyntax.mk_fst l,
                              v2 |-> pairSyntax.mk_snd l] th
          in SOME (PROVE_HYP (GSYM (ISPEC l PAIR)) th') end
        else NONE
      end handle HOL_ERR _ => NONE
    fun loop th =
      case List.find (fn th' => length (hyp th') < length (hyp th))
             (List.mapPartial (try th) (hyp th)) of
        SOME th' => loop th'
      | NONE => th
  in loop th end

fun split_hyps th =
  case List.find is_conj (hyp th) of
    NONE => th
  | SOME h =>
      let val (a, b) = dest_conj h in
        split_hyps (PROVE_HYP (CONJ (ASSUME a) (ASSUME b)) th)
      end

(* prefix: SPEC m P C Q; rule: SPEC m (R * cond K) C' Q' with R's resource
   arguments variables, instantiated by insts (by name) and at Q's
   resources; both framed and composed, K's conjuncts left as
   hypotheses, the variables named in keepn kept *)
fun call_step keepn insts prefix rule =
  let
    val rule0 = SPEC_ALL rule
    val (ren, _) =
      List.foldl (fn (v, (s, av)) =>
                    let val v' = variant av v in ((v |-> v') :: s, v' :: av) end)
                 ([], thm_frees prefix) (thm_frees rule0)
    val rule1 = INST ren rule0
    val rule1 = INST (map (fn (n, t) => var_named rule1 n |-> t) insts) rule1
                |> REWRITE_RULE [SPEC_MOVE_COND, GSYM AND_IMP_INTRO]
                |> UNDISCH_ALL |> split_hyps
    val (_, _, _, q1) = spec_parts prefix
    val (_, p2, _, _) = spec_parts rule1
    val (star, _, _) = dest_star q1
    val q1s = strip_star q1
    val theta = List.mapPartial (fn r2 =>
       case List.find (fn r1 => head_name r1 = head_name r2) q1s of
         SOME r1 => SOME (rand r2 |-> rand r1)
       | NONE => NONE) (strip_star p2)
    val rule2 = INST theta rule1
    val p2s = strip_star (#2 (spec_parts rule2))
    fun has xs r = List.exists (fn x => head_name x = head_name r) xs
    val f1 = List.filter (not o has q1s) p2s
    val f2 = List.filter (not o has p2s) q1s
    val pre1 = if null f1 then prefix
               else SPEC (mk_stars star f1) (MATCH_MP SPEC_FRAME prefix)
    val rule3 = if null f2 then rule2
                else SPEC (mk_stars star f2) (MATCH_MP SPEC_FRAME rule2)
    val eq = EQT_ELIM (star_eq_conv
               (mk_eq (#4 (spec_parts pre1), #2 (spec_parts rule3))))
    val th = MATCH_MP SPEC_COMPOSE
               (CONJ (CONV_RULE (RAND_CONV (REWR_CONV eq)) pre1) rule3)
    val th = CONV_RULE (RAND_CONV (SIMP_CONV bool_ss
               [CONJUNCT1 (SPEC_ALL SEP_CLAUSES)])) th
  in
    elim_defs (List.filter (fn v => mem (fst (dest_var v)) keepn)
                 (thm_frees th)) th
  end

fun strip_sep_exists t =
  if head_name t = "SEP_EXISTS" then
    let val (v, b) = dest_abs (rand t)
        val (vs, body) = strip_sep_exists b
    in (v :: vs, body) end
  else ([], t)

(* th: SPEC m P C (SEP_EXISTS xs. B0 xs * cond K). The code after it is
   composed through the summaries sums from B0, framed with cond K, and
   put under the existentials; its hypotheses that mention xs are passed
   to fix, which proves them from K and hypotheses free of xs *)
fun cont_step sums fix th =
  let
    val (m, _, c, q) = spec_parts th
    val (xs, body) = strip_sep_exists q
    val (star, _, _) = dest_star body
    val (conds, rs) = List.partition (fn f => head_name f = "cond")
                        (strip_star body)
    val k = case conds of [cnd] => rand cnd
                        | _ => raise mk_HOL_ERR "wrappedEtherWithdraw"
                                 "cont_step" "conds"
    val b0 = mk_stars star rs
    val eqB = EQT_ELIM (star_eq_conv
                (mk_eq (body, list_mk_comb (star, [b0, hd conds]))))
    val empty = pred_setSyntax.mk_empty
                  (pred_setSyntax.dest_set_type (type_of c))
    val (reg, _) = compose_region path_config sums
                     (ISPECL [m, b0, empty] SPEC_REFL)
    val reg1 = reg |> REWRITE_RULE [SPEC_MOVE_COND, GSYM AND_IMP_INTRO]
                   |> UNDISCH_ALL |> split_hyps
    val kth = ASSUME k
    val reg2 = List.foldl (fn (h, th) =>
                 if List.exists (fn x => free_in x h) xs
                 then PROVE_HYP (fix kth h) th else th) reg1 (hyp reg1)
    val eqP = EQT_ELIM (star_eq_conv (mk_eq (#2 (spec_parts reg2), b0)))
    val reg3 = CONV_RULE (RATOR_CONV (RATOR_CONV (RAND_CONV
                 (REWR_CONV eqP)))) reg2
    val (_, _, c3, q3) = spec_parts reg3
    val reg4 = EQ_MP (GSYM (ISPECL [m, b0, c3, q3, k] SPEC_MOVE_COND))
                 (DISCH k reg3)
    val reg4 = EQ_MP (PART_MATCH lhs SPEC_MOVE_COND_POST (concl reg4)) reg4
    val reg5 = CONV_RULE (RATOR_CONV (RATOR_CONV (RAND_CONV
                 (REWR_CONV (GSYM eqB))))) reg4
    val ex = List.foldr (fn (x, th) =>
               HO_MATCH_MP SPEC_EXISTS_EXISTS (GEN x th)) reg5 xs
  in
    MATCH_MP SPEC_COMPOSE (CONJ th ex)
  end

fun reads_tac g =
  (CONV_TAC (QCONV (with_ground_div reads_conv))
   \\ RULE_ASSUM_TAC (CONV_RULE (QCONV (with_ground_div reads_conv)))) g

(* a hypothesis h of the code after the CALL that mentions the callee's
   outcome: from K, or else from h at gasLeft 0 for both values of
   success, the code's gas checks being monotone in gasLeft *)
fun gas_fix0 h =
  let
    fun named n = List.find (fn v => fst (dest_var v) = n) (free_vars h)
    val h0 = case named "gasLeft" of
               SOME gl => subst [gl |-> numSyntax.zero_tm] h | NONE => h
    val sv = named "success"
    val hs = case sv of
               SOME v => [subst [v |-> T] h0, subst [v |-> F] h0]
             | NONE => [h0]
    val hs = map (fn t => rhs (concl (QCONV (SIMP_CONV std_ss []) t))) hs
    val tac = strip_tac
      \\ (case sv of SOME v => Cases_on [ANTIQUOTE v] | NONE => ALL_TAC)
      \\ fs[] \\ rpt strip_tac \\ fs[] \\ decide_tac
  in
    MP (prove (mk_imp (list_mk_conj hs, h), tac)) (LIST_CONJ (map ASSUME hs))
  end

fun gas_fix kth h =
  MP (prove (mk_imp (concl kth, h), DISCH_TAC \\ reads_tac \\ fs[])) kth
  handle HOL_ERR _ => gas_fix0 h
       | Conv.UNCHANGED => gas_fix0 h

(* ---------------------------------------------------------------- *)
(* The withdraw path

   The selector chain to withdraw at 98, the callvalue check at 579, the
   argument decoding at 590, withdraw at 2521: the balance check, the
   balance update and the CALL at 2724 sending wad to the caller. After
   it, 2725 tests the CALL's success: if it succeeded, the Withdrawal log
   at 2740 and the return to the STOP at 612; if it failed, the REVERT at
   2736. *)

val withdraw_prefix =
  compose_path
    [(0, "_skip"), (13, "_skip"), (65, "_skip"), (76, "_skip"),
     (87, "_skip"), (98, "_take"), (579, "_take"), (590, "_Jump"),
     (2521, "_take"), (2599, "")]

val withdraw_call =
  call_step ["dynamicGas", "calleeGas"] [("call_inst", “Call”)]
    withdraw_prefix SPEC_Call_stipend
  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [call_has_value_def]))
  |> (fn th => SPEC “evm_Contexts cs” (MATCH_MP SPEC_FRAME th))
  |> CONV_RULE (RAND_CONV (SIMP_CONV bool_ss
       [CONJUNCT1 (SPEC_ALL SEP_CLAUSES)]))

val withdraw_whole =
  cont_step [weth_block 2725 "_take", weth_block 2725 "_skip",
             weth_block 2740 "_Jump", weth_block 612 "_outermost",
             weth_block 2736 "_outermost"] gas_fix withdraw_call
  |> elim_defs []

fun find_hyp f th = valOf (List.find f (hyp th))

(* the domain collects (Collect dd), so the slots added before the CALL
   are in it *)
val withdraw_inst =
  let
    val th = withdraw_whole
    fun is_msd h = is_eq h andalso head_name (lhs h) = "msdomain_add_slot"
    val msd = find_hyp is_msd th
    val d = var_named th "d"
    val dd = mk_var ("dd", “:domain”)
    val dd' = subst [d |-> “Collect ^dd”] (lhs msd)
              |> SIMP_CONV (srw_ss()) [msdomain_add_slot_def]
              |> concl |> rhs |> rand
    val th = INST [rand (rhs msd) |-> dd', d |-> “Collect ^dd”] th
  in
    PROVE_HYP (EQT_ELIM (SIMP_CONV (srw_ss()) [msdomain_add_slot_def]
                           (find_hyp is_msd th))) th
  end

(* the delegation's cost, accesses and domain after the CALL, which
   delegate_check relates to its other arguments, made functions of them *)
fun delegate_witnesses th =
  let
    val dh = find_term (fn t => head_name t = "delegate_check") (concl th)
    val (c, dm, rb, dc, nrb, nd) = case snd (strip_comb dh) of
        [a, b, c, d, e, f] => (a, b, c, d, e, f)
      | _ => raise mk_HOL_ERR "wrappedEtherWithdraw" "delegate_witnesses" ""
  in
    INST [dc |-> “case get_delegate ^c of NONE => 0
                    | SOME del => access_cost ^rb del”,
          nrb |-> “case get_delegate ^c of NONE => ^rb
                     | SOME del => accesses_add del ^rb”,
          nd |-> “case get_delegate ^c of NONE => ^dm
                    | SOME del => msdomain_add del ^dm”] th
  end

(* ground byte lists, such as a balance slot's index, evaluated *)
val ground_reverse_conv =
  ONCE_DEPTH_CONV (fn t =>
    if is_app "REVERSE" 1 t andalso null (free_vars t) then EVAL t
    else NO_CONV t)

(* hypotheses that hold at the start folded into the precondition *)
val withdraw_spec =
  let
    val th = spec_start withdraw_inst
    val th = INST [var_named th "returnCode" |-> F] th
    val th = List.foldl (fn (h, th) =>
               PROVE_HYP (EQT_ELIM (QCONV (SIMP_CONV (srw_ss()) []) h)) th
               handle HOL_ERR _ => th) th
               (List.filter (fn h => term_size h < 200) (hyp th))
    val th1 = DISCH_ALL th |> REWRITE_RULE [AND_IMP_INTRO]
    val (h, sp) = dest_imp (concl th1)
    val (m, p, c, q) = spec_parts (ASSUME sp)
  in
    EQ_MP (GSYM (ISPECL [m, p, c, q, h] SPEC_MOVE_COND)) th1
    |> path_reads
    |> CONV_RULE (RATOR_CONV (RAND_CONV
         (PURE_REWRITE_CONV [INSERT_UNION_EQ, UNION_EMPTY])))
    |> CONV_RULE ground_reverse_conv
    |> path_keys |> spec_code |> spec_pool |> delegate_witnesses
  end

Theorem STAR_if[local]:
  STAR x (if c then a else b) = (if c then STAR x a else STAR x b) ∧
  STAR (if c then a else b) y = (if c then STAR a y else STAR b y)
Proof
  rw[]
QED

Theorem evm_Exception_INR_ISR[local]:
  (if c then evm_Exception (INR x) * R1 else evm_Exception (INR y) * R2)
    (evm2set (r, t)) ⇒ ISR r
Proof
  Cases_on `c` \\ simp[evm2set_def, STAR_evm2set] \\ rw[] \\ simp[]
QED

(* the factors named by names first, in order, then the others with the
   conditions last *)
fun order_conv names tm =
  let
    val (star, _, _) = dest_star tm
    val fs = strip_star tm
    val picked = map (fn n => valOf (List.find (fn f => head_name f = n) fs))
                   names
    val others = List.filter (fn f => not (mem (head_name f) names)) fs
    val (conds, others) = List.partition (fn f => head_name f = "cond")
                            others
    val tm' = mk_stars star (picked @ [mk_stars star (others @ conds)])
  in
    EQT_ELIM (star_eq_conv (mk_eq (tm, tm')))
  end

fun push_if_conv tm =
  if can dest_star tm then
    (BINOP_CONV (TRY_CONV push_if_conv) THENC
     TRY_CONV (FIRST_CONV (map REWR_CONV (CONJUNCTS STAR_if)))) tm
  else NO_CONV tm

fun under_exists c tm =
  if head_name tm = "SEP_EXISTS" then RAND_CONV (ABS_CONV (under_exists c)) tm
  else c tm

(* the postcondition as SEP_EXISTS xs. if c then A else B with A, B in the
   order run_to_run_transaction and run_to_run_transaction_failure name *)
val withdraw_post_conv =
  SIMP_CONV bool_ss [CONJUNCT1 (SPEC_ALL SEP_CLAUSES),
                     CONJUNCT1 (CONJUNCT2 (SPEC_ALL SEP_CLAUSES))]
  THENC under_exists push_if_conv
  THENC under_exists
    (RATOR_CONV (RAND_CONV (order_conv
       ["evm_Exception", "evm_ReturnData", "evm_Logs", "evm_Rollback",
        "evm_Contexts", "evm_GasUsed", "evm_MsgParams", "evm_AddRefund",
        "evm_SubRefund", "evm_TxParams"])) THENC
     RAND_CONV (order_conv
       ["evm_Exception", "evm_ReturnData", "evm_Contexts", "evm_GasUsed",
        "evm_MsgParams", "evm_TxParams"]))

(* from a state s1 meeting the precondition, run ends in the postcondition *)
val withdraw_lift =
  let
    val th = CONV_RULE (RAND_CONV withdraw_post_conv) withdraw_spec
    val th = MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] run_from_SPEC_halts)
               th
    val (_, rest) = dest_imp (concl th)
    val (isr, _) = dest_imp rest
    val isr_th = prove (isr,
      rpt gen_tac \\ Ho_Rewrite.PURE_REWRITE_TAC [SEP_EXISTS_THM]
      \\ rewrite_tac [GSYM STAR_ASSOC]
      \\ strip_tac
      \\ pop_assum (ACCEPT_TAC o MATCH_MP evm_Exception_INR_ISR))
  in
    UNDISCH th |> C MP isr_th |> DISCH_ALL
  end

Theorem w2w_w2w_address[local]:
  w2w (w2w (a:address) : bytes32) = a
Proof
  simp[w2w_w2w, WORD_ALL_BITS, w2w_id]
QED

Theorem access_cost_le[local]:
  access_cost rb a ≤ 2600
Proof
  rw[access_cost_def, warm_access_cost_def, cold_access_cost_def]
QED

Theorem accesses_add_slot_twice[local]:
  accesses_add_slot a (accesses_add_slot a rb) = accesses_add_slot a rb
Proof
  simp[accesses_add_slot_def, rollback_state_component_equality,
       access_sets_component_equality]
QED

Theorem fINSERT_twice[local]:
  fINSERT a ∘ fINSERT a = fINSERT a
Proof
  simp[FUN_EQ_THM]
QED

Theorem call_gas_le[local]:
  FST (call_gas v g gl mc oc) ≤ g + oc ∧
  SND (call_gas v g gl mc oc) ≤ g + call_stipend
Proof
  rw[call_gas_def, LET_THM, MIN_DEF]
QED

Theorem delegate_cost_le[local]:
  (case get_delegate c of NONE => 0 | SOME del => access_cost rb del) ≤ 2600
Proof
  CASE_TAC \\ simp[access_cost_le]
QED

Theorem transfer_gas_le[local]:
  w2n (2300w * b2w b : bytes32) ≤ 2300
Proof
  Cases_on `b` \\ simp[]
QED

Theorem transfer_call_gas_le[local]:
  SND (call_gas v (w2n (2300w * b2w (v = 0) : bytes32)) gl mc oc) ≤ 2300
Proof
  Cases_on `v = 0` \\ rw[call_gas_def, call_stipend_def, LET_THM, MIN_DEF]
QED

Theorem COND_zero_le[local]:
  (if b then x else 0n) ≤ x
Proof
  rw[]
QED

(* the gas side conditions of the withdraw path: ground memory costs
   evaluated, every cost bounded by its worst case *)
fun is_ground_let t = is_let t andalso null (free_vars t)
val ground_let_tac =
  CONV_TAC (DEPTH_CONV (fn t => if is_ground_let t then EVAL t
                                else NO_CONV t))
fun bound_terms_tac (asl, w) =
  let
    val fvs = free_vars w
    fun closed t = List.all (fn v => tmem v fvs) (free_vars t)
    fun bound t =
      if is_app "access_cost" 2 t andalso closed t then
        SOME (PART_MATCH (rand o rator) access_cost_le t)
      else if is_app "FST" 1 t andalso is_app "call_gas" 5 (rand t) then
        SOME (PART_MATCH (rand o rator) (CONJUNCT1 call_gas_le) t)
      else if is_app "SND" 1 t andalso is_app "call_gas" 5 (rand t) then
        SOME (PART_MATCH (rand o rator) transfer_call_gas_le t
              handle HOL_ERR _ =>
              PART_MATCH (rand o rator) (CONJUNCT2 call_gas_le) t)
      else if is_app "w2n" 1 t andalso closed t then
        SOME (PART_MATCH (rand o rator) transfer_gas_le t)
          handle HOL_ERR _ => NONE
      else if is_cond t andalso closed t then
        SOME (PART_MATCH (rand o rator) COND_zero_le t)
          handle HOL_ERR _ => NONE
      else if TypeBase.is_case t andalso closed t then
        SOME (PART_MATCH (rand o rator) delegate_cost_le t)
          handle HOL_ERR _ => NONE
      else NONE
    val ths = List.mapPartial bound
                (HOLset.listItems (HOLset.addList (empty_tmset,
                   find_terms (K true) w)))
  in
    MAP_EVERY assume_tac ths (asl, w)
  end

Theorem rollback_accounts_I[local]:
  (λr. r with accounts updated_by I) = I ∧
  (s:execution_state) with rollback updated_by I = s
Proof
  rw[FUN_EQ_THM, rollback_state_component_equality,
     execution_state_component_equality]
QED

(* the precondition's conjuncts, by kind: the gas sums, the delegation
   check after the CALL, and the rest *)
fun mentions name t =
  can (find_term (fn u => is_const u andalso fst (dest_const u) = name)) t
val gasLimit_sel = rator “(p:message_parameters).gasLimit”
fun is_gas_goal t =
  can (find_term (fn u => is_comb u andalso same_const (rator u) gasLimit_sel)) t
  orelse mentions "call_gas" t
fun on_goals p tac (g as (_, w)) = if p w then tac g else ALL_TAC g
(* the domain side conditions: a field in the domain left after the code *)
fun is_domain_goal t = pred_setSyntax.is_in t orelse pred_setSyntax.is_subset t

val withdraw_rest_tac =
  simp[transfer_value_zero, rollback_accounts_I,
       execution_state_component_equality,
       rollback_state_component_equality, fmap_entries_def,
       SIMP_RULE std_ss [APPEND] withdraw_selector_calldata,
       DROP_APPEND, DROP_LENGTH_TOO_LONG, calldata_word,
       mask_and_w2w, balance_slot_key_bytes, access_slot_check_def]
  \\ qpat_x_assum `LENGTH tx.data ≤ _` mp_tac
  \\ asm_simp_tac (srw_ss()) [ADD1]
  \\ strip_tac \\ DEP_REWRITE_TAC [LESS_MOD] \\ simp[]

val withdraw_delegate_tac =
  simp[delegate_check_def] \\ CASE_TAC
  \\ simp[access_check_def, msdomain_add_def, msdomain_add_slot_def]

(* abbreviates the costs bounded as wholes, leaving decide_tac a linear
   goal *)
fun gen_costs_tac (asl, w) =
  let
    fun big t = TypeBase.is_case t orelse
                (is_app "FST" 1 t andalso is_app "call_gas" 5 (rand t))
    val ts = HOLset.listItems (HOLset.addList (empty_tmset, find_terms big w))
    val vs = List.tabulate (length ts,
               fn i => mk_var ("cost" ^ Int.toString i, numSyntax.num))
  in
    MAP_EVERY (fn (v, t) => markerLib.ABBREV_TAC (mk_eq (v, t)))
      (ListPair.zip (vs, ts)) (asl, w)
  end

val withdraw_gas_tac =
  CONV_TAC (QCONV word_of_bytes_conv)
  \\ asm_simp_tac (srw_ss())
    [transfer_value_zero, rollback_accounts_I,
     execution_state_component_equality,
     rollback_state_component_equality, fmap_entries_def,
     SIMP_RULE std_ss [APPEND] withdraw_selector_calldata,
     DROP_APPEND, DROP_LENGTH_TOO_LONG, calldata_word,
     mask_and_w2w, balance_slot_key_bytes, access_slot_check_def,
     access_slot_cost_add_slot, SStore_gas_add_slot,
     accesses_add_slot_accounts, call_stipend_def]
  \\ ground_let_tac
  \\ qpat_assum `s.originalAccounts = _` (fn th => rewrite_tac[th])
  \\ qpat_assum `lookup_account addr s.rollback.accounts = _`
       (fn th => rewrite_tac[th])
  \\ TRY (qmatch_goalsub_abbrev_tac `sstore_base_gas c0 c0 v0`
           \\ `sstore_base_gas c0 c0 v0 ≤ 2900`
                by (irule sstore_base_gas_same_le
                    \\ qunabbrevl_tac [`c0`, `v0`] \\ strip_tac \\ gvs[]))
  \\ gas_bounds_tac \\ bound_terms_tac
  \\ PURE_REWRITE_TAC [new_account_cost_def, call_value_cost_def]
  \\ RULE_ASSUM_TAC (PURE_REWRITE_RULE [new_account_cost_def,
                                         call_value_cost_def])
  \\ gen_costs_tac \\ decide_tac

Theorem not_is_code_dest[local]:
  ¬is_code_dest d ⇒ ∃m. d = Memory m
Proof
  Cases_on `d` \\ rw[is_code_dest_def]
QED

Theorem lookup_account_transfer_value_from[local]:
  x ≠ y ⇒
  lookup_account x (transfer_value x y v accs) =
  lookup_account x accs with balance := (lookup_account x accs).balance - v
Proof
  rw[transfer_value_def, lookup_account_def, update_account_def,
     APPLY_UPDATE_THM, account_state_component_equality]
QED

(* the CALL pays only a nonzero wad, so the storage write after it is the
   same either way *)
Theorem COND_transfer_value[local]:
  (if 0 < v then
     transfer_value x y v
       (SStore_write a k (s0 + -1w * n2w v) rb).accounts
   else (SStore_write a k s0 rb).accounts) =
  transfer_value x y v (SStore_write a k (s0 + -1w * n2w v) rb).accounts
Proof
  Cases_on `v` \\ simp[transfer_value_def]
QED

Theorem SStore_write_fields[local]:
  (SStore_write x k v rb).toDelete = rb.toDelete ∧
  (accesses_add_slot sk rb).toDelete = rb.toDelete ∧
  lookup_account a (SStore_write x k v rb).accounts =
    if a = x then
      lookup_account x rb.accounts with
        storage := update_storage k v (lookup_account x rb.accounts).storage
    else lookup_account a rb.accounts
Proof
  rewrite_tac[SStore_write_def, accesses_add_slot_def,
              sstore_write_accounts_updater_def]
  \\ simp_tac (srw_ss()) [LET_THM]
  \\ Cases_on `a = x`
  >- gvs[lookup_account_update_account_same,
         account_state_component_equality]
  \\ asm_simp_tac (srw_ss()) [lookup_account_update_account_other]
QED

Theorem word_add_neg_mul[local]:
  (a:bytes32) + -1w * b = a - b
Proof
  simp[]
QED

(* evaluates the largest w2n of a memory read in the goal, so that the
   reads of a log's offset and length are separate steps *)
fun read_w2n_tac (g as (_, w)) =
  let
    fun reads_memory t =
      is_app "w2n" 1 t andalso can (find_term (is_app "expanded_memory" 3)) t
    val ts = find_terms reads_memory w
    val t = hd (Listsort.sort (fn (a, b) =>
                  Int.compare (term_size b, term_size a)) ts)
  in
    PURE_REWRITE_TAC [QCONV (with_ground_div reads_conv) t] g
  end

(* the leading SEP_EXISTSs of an assertion applied to a state, as ∃s,
   without rewriting inside the (large) assertion *)
fun sep_exists_conv t =
  ((HO_REWR_CONV SEP_EXISTS_THM THENC BINDER_CONV sep_exists_conv)
   ORELSEC ALL_CONV) t

fun is_key_term t =
  is_app "word_of_bytes" 3 t andalso
  can (find_term (is_app "Keccak_256_w64" 1)) t

(* rewrites the balance slot key the path hashes in memory to
   balance_slot_key tx.from *)
fun key_tac (g as (asl, _)) =
  let val k = find_term is_key_term (list_mk_conj asl) in
    (sg ‘^k = balance_slot_key tx.from’
     >- (CONV_TAC (QCONV (with_ground_div reads_conv))
         \\ CONV_TAC ground_reverse_conv
         \\ rewrite_tac[balance_slot_key_bytes])
     \\ pop_assum (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]))) g
  end

(* withdraw(wad) with wad at most the caller's balance: either the CALL
   paying the caller succeeds, and the balance slot is debited, wad paid
   and logged; or it fails and the transaction reverts. A safety statement:
   it doesn't say when the CALL fails *)
Theorem weth_withdraw_run_transaction:
  (lookup_account addr accounts).code = contract_code ∧
  zero_value_call (Collect dd, chainId, prevHashes, blk) accounts tx addr
    (function_selector "withdraw" [Uint 256] ++
     enc (Tuple [Uint 256]) (ListV [NumV wad])) 60000 s ∧
  wad ≤ w2n (lookup_storage (balance_slot_key tx.from)
               (lookup_account addr accounts).storage) ∧
  ¬fIN tx.from precompile_addresses ∧
  blk.coinBase ≠ addr
  ⇒
  ∃result accounts'.
    run_transaction (Collect dd) F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    (∀a. a ≠ addr ⇒
         (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    ((result.result = NONE ∧
      result.output = [] ∧
      (∃calleeLogs.
         result.logs =
           calleeLogs ++
           [<| logger := addr;
               topics :=
                 [word_of_bytes_be
                    (Keccak_256_string "Withdrawal(address,uint256)");
                  w2w tx.from];
               data := enc (Tuple [Uint 256]) (ListV [NumV wad]) |>]) ∧
      (lookup_account tx.from s.rollback.accounts).balance + wad ≤
        (lookup_account tx.from accounts').balance ∧
      lookup_account addr accounts' =
        let acc = lookup_account addr accounts;
            ks = balance_slot_key tx.from
        in acc with <| balance := acc.balance - wad;
                       storage := update_storage ks
                         (lookup_storage ks acc.storage - n2w wad)
                         acc.storage |>) ∨
     (result.result = SOME Reverted ∧
      result.output = [] ∧
      result.logs = [] ∧
      lookup_account addr accounts' = lookup_account addr accounts))
Proof
  PURE_REWRITE_TAC [cv_eval “word_of_bytes_be (Keccak_256_string
                       "Withdrawal(address,uint256)") : bytes32”,
                    withdraw_value_enc, zero_value_call_def]
  \\ strip_tac
  \\ strip_assume_tac contract_code_not_delegation
  \\ drule_all initial_state_call_code \\ strip_tac
  \\ drule initial_state_contract
  \\ disch_then (qspec_then `addr` mp_tac)
  \\ impl_tac >- gvs[]
  \\ strip_tac
  \\ fs[GSYM parsed_contract_code_def]
  \\ drule_all wf_initial_state \\ strip_tac
  \\ `∃rest. tx.data = [0x2Ew; 0x1Aw; 0x7Dw; 0x4Dw] ++
                       word_to_bytes (n2w wad : bytes32) T ++ rest`
  by (qpat_x_assum `_ ≼ tx.data` mp_tac
      \\ rewrite_tac[withdraw_selector_eq, IS_PREFIX_APPEND]
      \\ strip_tac \\ simp[])
  \\ `wad < dimword (:256)`
  by (qspec_then `lookup_storage (balance_slot_key tx.from)
                    (lookup_account addr accounts).storage`
        assume_tac w2n_lt
      \\ decide_tac)
  \\ `ctxt.msgParams.caller = tx.from ∧ ¬ctxt.msgParams.static` by gvs[]
  \\ mp_tac (Q.INST [‘p’ |-> ‘ctxt.msgParams’, ‘rb’ |-> ‘s.rollback’,
                     ‘rd’ |-> ‘[]’, ‘l’ |-> ‘[]’,
                     ‘ar’ |-> ‘0’, ‘sr’ |-> ‘0’,
                     ‘original’ |-> ‘s.originalAccounts’,
                     ‘txParams’ |-> ‘s.txParams’,
                     ‘s1’ |-> ‘s with rollback updated_by
                       (λr. r with accounts updated_by
                              transfer_value tx.from addr tx.value)’]
                    withdraw_lift)
  \\ impl_tac
  >- (
    simp_tac pure_ss [evm2set_def, GSYM STAR_ASSOC]
    \\ rewrite_tac[STAR_evm2set, STAR_evm_OriginalAccounts,
                   STAR_CODE_POOL_evm2set, cond_STAR, SEP_T_def]
    \\ PURE_REWRITE_TAC [execution_state_accfupds]
    \\ qpat_assum `s.contexts = _` (fn th => PURE_REWRITE_TAC [th, HD, FST])
    \\ rpt conj_tac
    \\ on_goals is_domain_goal (simp_tac (srw_ss()) [])
    \\ simp_tac (srw_ss()) [call_has_value_def, is_call_def,
                            w2w_w2w_address, w2w_id]
    \\ rpt conj_tac
    \\ on_goals (fn w => not (is_gas_goal w) andalso
                          not (mentions "delegate_check" w)) withdraw_rest_tac
    \\ on_goals (mentions "delegate_check") withdraw_delegate_tac
    \\ on_goals is_gas_goal withdraw_gas_tac)
  \\ strip_tac
  \\ qpat_x_assum `$SEP_EXISTS _ _`
       (strip_assume_tac o CONV_RULE sep_exists_conv)
  \\ qpat_assum `ctxt.msgParams.parsed = _` (fn th1 =>
       qpat_assum `ctxt.msgParams.code = _` (fn th2 =>
         qpat_x_assum `(if _ then _ else _) _`
           (assume_tac o REWRITE_RULE [th1, th2])))
  \\ Cases_on `success`
  \\ qpat_x_assum `(if _ then _ else _) _` (assume_tac o REWRITE_RULE [])
  \\ qpat_assum `(_ * _) (evm2set rs2)`
       (strip_assume_tac o REWRITE_RULE [STAR_ASSOC, cond_STAR])
  >- (
    drule_all run_to_run_transaction \\ strip_tac
    \\ qexistsl_tac [`result`, `accounts'`]
    \\ rpt (qpat_x_assum `(_ * _) (evm2set rs2)` kall_tac)
    \\ qpat_x_assum `gasLeft ≤ _` kall_tac
    \\ qpat_x_assum `run _ = SOME rs2` kall_tac
    \\ qpat_x_assum `¬is_code_dest _`
         (strip_assume_tac o MATCH_MP not_is_code_dest)
    \\ `word_of_bytes F 0w (REVERSE (take_pad_0 32
           (DROP 4 (buffer_to_list ctxt.msgParams.data)))) = n2w wad : bytes32`
    by (qpat_assum `ctxt.msgParams.data = _` (fn th => rewrite_tac[th])
        \\ qpat_assum `tx.data = _` (fn th => rewrite_tac[th])
        \\ simp_tac (srw_ss()) [DROP_APPEND, DROP_LENGTH_TOO_LONG,
                                calldata_word])
    \\ pop_assum (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]))
    \\ `w2n (n2w wad : bytes32) = wad`
    by (qpat_x_assum `wad < _` mp_tac \\ simp_tac (srw_ss()) [])
    \\ pop_assum (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]))
    \\ qpat_assum `ctxt.msgParams.caller = _` (fn c =>
         qpat_assum `ctxt.msgParams.callee = _` (fn e =>
         qpat_assum `s.rollback.toDelete = _` (fn d =>
           qpat_x_assum `rb'.accounts = _` (assume_tac o PURE_REWRITE_RULE
             [c, e, w2w_w2w_address])
           \\ qpat_x_assum `rb'.toDelete = _` (assume_tac o PURE_REWRITE_RULE
             [d, SStore_write_fields])
           \\ qpat_x_assum `result.logs = _` (assume_tac o PURE_REWRITE_RULE
             [c, e, APPEND]))))
    \\ key_tac
    \\ qpat_x_assum `rb'.accounts = _`
         (assume_tac o PURE_REWRITE_RULE [COND_transfer_value])
    \\ qpat_assum `rb'.toDelete = _` (fn t1 =>
         qpat_assum `rb'.accounts = _` (fn t2 =>
           qpat_x_assum `∀a. lookup_account a accounts' = _`
             (assume_tac o PURE_REWRITE_RULE [t1, t2, MEM, COND_CLAUSES] o
              BETA_RULE o PURE_REWRITE_RULE
                [ASSUME “ctxt.msgParams.outputTo = Memory m”,
                 TypeBase.case_def_of “:return_destination”])))
    \\ conj_tac >- first_assum ACCEPT_TAC
    \\ conj_tac
    >- (rpt strip_tac
        \\ qpat_x_assum `∀a. lookup_account a accounts' = _`
             (qspec_then `a` SUBST1_TAC)
        \\ simp[lookup_account_transfer_value_fields, SStore_write_fields])
    \\ disj1_tac
    \\ conj_tac >- first_assum ACCEPT_TAC
    \\ conj_tac >- first_assum ACCEPT_TAC
    \\ conj_tac
    >- (qexists_tac `calleeLogs`
        \\ qpat_x_assum `result.logs = _` SUBST1_TAC
        \\ read_w2n_tac \\ read_w2n_tac
        \\ CONV_TAC (QCONV (with_ground_div reads_conv))
        \\ rewrite_tac[REVERSE_word_to_bytes_bytes32])
    \\ conj_tac
    >- (qpat_x_assum `∀a. lookup_account a accounts' = _`
          (qspec_then `tx.from` SUBST1_TAC)
        \\ qpat_assum `addr ≠ tx.from` (fn th =>
             rewrite_tac[MATCH_MP lookup_account_transfer_value_to th,
                         SStore_write_fields, EQF_INTRO (GSYM th),
                         accesses_add_slot_accounts])
        \\ simp_tac (srw_ss()) []
        \\ irule (DECIDE “a ≤ b ⇒ a ≤ b + c + d:num”)
        \\ decide_tac)
    \\ qpat_x_assum `∀a. lookup_account a accounts' = _`
         (qspec_then `addr` SUBST1_TAC)
    \\ qpat_assum `addr ≠ tx.from` (fn t1 =>
         qpat_assum `blk.coinBase ≠ addr` (fn t2 =>
           rewrite_tac[t1, GSYM t2, word_add_neg_mul, ADD_0,
                       MATCH_MP lookup_account_transfer_value_from t1,
                       SStore_write_fields, accesses_add_slot_accounts]))
    \\ qpat_assum `lookup_account addr s.rollback.accounts = _`
         (fn th => rewrite_tac[th])
    \\ simp_tac (srw_ss()) [LET_THM, account_state_component_equality])
  \\ drule_all run_to_run_transaction_failure \\ strip_tac
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ rpt (qpat_x_assum `(_ * _) (evm2set rs2)` kall_tac)
  \\ qpat_x_assum `run _ = SOME rs2` kall_tac
  \\ qpat_x_assum `rb' = _` kall_tac
  \\ qpat_x_assum `gasLeft ≤ _` kall_tac
  \\ qpat_x_assum `result.gasUsed = _` kall_tac
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ qpat_x_assum `accounts' = _` SUBST_ALL_TAC
  \\ conj_tac
  >- rewrite_tac[lookup_account_pay_transaction_gas, account_state_accfupds]
  \\ disj2_tac
  \\ rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qpat_x_assum `result.output = _` SUBST1_TAC \\ EVAL_TAC)
  >- first_assum ACCEPT_TAC
  \\ rewrite_tac[lookup_account_pay_transaction_gas]
  \\ qpat_assum `addr ≠ tx.from` (fn t1 =>
       qpat_assum `blk.coinBase ≠ addr` (fn t2 =>
         rewrite_tac[t1, GSYM t2]))
  \\ qpat_assum `lookup_account addr s.rollback.accounts = _`
       (fn th => rewrite_tac[th])
  \\ simp_tac (srw_ss()) [account_state_component_equality]
QED

(* ---------------------------------------------------------------- *)
(* The same over the WETH_EVM relation *)

Theorem lookup_update_storage[local]:
  lookup_storage k (update_storage k' v s) =
  if k' = k then v else lookup_storage k s
Proof
  rw[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
QED

Theorem WETH_withdraw_fields[local]:
  (WETH_withdraw a n ws).touched = ws.touched ∧
  (WETH_withdraw a n ws).balances = (a =+ ws.balances a - n) ws.balances ∧
  (WETH_withdraw a n ws).locked = ws.locked - n
Proof
  rw[WETH_withdraw_def]
QED

(* the storage write of a withdrawal keeps the WETH_EVM relation *)
Theorem WETH_withdraw_allowance_fields[local]:
  (WETH_withdraw a n ws).allowances = ws.allowances ∧
  (WETH_withdraw a n ws).allowances_touched = ws.allowances_touched
Proof
  rw[WETH_withdraw_def]
QED

(* a withdrawal's balance write keeps the allowance slots: if the caller's
   balance slot is an allowance slot the relation covers, the caller is
   untouched, so its balance and wad are 0 and the write is a no-op *)
Theorem WETH_withdraw_allowance_storage[local]:
  wf_WETH_state ws ∧ n ≤ ws.balances src ∧
  lookup_storage (balance_slot_key src) st = n2w (ws.balances src) ∧
  (∀owner spender.
     allowance_slot_key owner spender ∉ {0w; 1w; 2w} ∧
     allowance_slot_key owner spender ∉ IMAGE balance_slot_key ws.touched ∧
     ((owner, spender) ∈ ws.allowances_touched ∨
      allowance_slot_key owner spender ∉
        IMAGE (λ(owner, spender). allowance_slot_key owner spender)
          ws.allowances_touched) ⇒
     lookup_storage (allowance_slot_key owner spender) st =
       n2w (ws.allowances owner spender)) ⇒
  (∀owner spender.
     allowance_slot_key owner spender ∉ {0w; 1w; 2w} ∧
     allowance_slot_key owner spender ∉ IMAGE balance_slot_key (WETH_withdraw src n ws).touched ∧
     ((owner, spender) ∈ (WETH_withdraw src n ws).allowances_touched ∨
      allowance_slot_key owner spender ∉
        IMAGE (λ(owner, spender). allowance_slot_key owner spender)
          (WETH_withdraw src n ws).allowances_touched) ⇒
     lookup_storage (allowance_slot_key owner spender) (update_storage (balance_slot_key src) (lookup_storage (balance_slot_key src) st - n2w n) st) =
       n2w ((WETH_withdraw src n ws).allowances owner spender))
Proof
  rewrite_tac[WETH_withdraw_fields, WETH_withdraw_allowance_fields]
  \\ strip_tac \\ rpt gen_tac
  \\ disch_then (fn th => assume_tac th
       \\ first_x_assum (assume_tac o C MATCH_MP th))
  \\ rewrite_tac[lookup_update_storage]
  \\ Cases_on `balance_slot_key src = allowance_slot_key owner spender`
  >- (
    `src ∉ ws.touched` by metis_tac[IN_IMAGE]
    \\ `ws.balances src = 0`
       by (gvs[wf_WETH_state_def, SUBSET_DEF] \\ metis_tac[NOT_ZERO_LT_ZERO])
    \\ `n = 0` by decide_tac
    \\ gvs[])
  \\ asm_rewrite_tac[]
QED

Theorem WETH_withdraw_storage[local]:
  wf_WETH_state ws ∧ n ≤ ws.balances src ∧
  (∀a. balance_slot_key a ∉ {0w; 1w; 2w} ∧
       (a ∈ ws.touched ∨ balance_slot_key a ∉ IMAGE balance_slot_key ws.touched) ⇒
       lookup_storage (balance_slot_key a) st = n2w (ws.balances a)) ∧
  (∀b. b ∈ ws.touched ∧ balance_slot_key b = balance_slot_key src ⇒ b = src) ∧
  balance_slot_key src ∉ {0w; 1w; 2w}
  ⇒
  let st' = update_storage (balance_slot_key src)
              (lookup_storage (balance_slot_key src) st - n2w n) st;
      ws' = WETH_withdraw src n ws in
  wf_WETH_state ws' ∧
  (∀a. balance_slot_key a ∉ {0w; 1w; 2w} ∧
       (a ∈ ws'.touched ∨
        balance_slot_key a ∉ IMAGE balance_slot_key ws'.touched) ⇒
       lookup_storage (balance_slot_key a) st' = n2w (ws'.balances a)) ∧
  lookup_storage 0w st' = lookup_storage 0w st ∧
  lookup_storage 1w st' = lookup_storage 1w st ∧
  lookup_storage 2w st' = lookup_storage 2w st
Proof
  strip_tac
  \\ `∀a. a ∉ ws.touched ⇒ ws.balances a = 0`
     by (gvs[wf_WETH_state_def, SUBSET_DEF] \\ metis_tac[NOT_ZERO_LT_ZERO])
  \\ `lookup_storage (balance_slot_key src) st = n2w (ws.balances src)`
     by (first_assum irule \\ simp[] \\ metis_tac[])
  \\ simp_tac std_ss [LET_THM]
  \\ conj_tac >- (irule wf_WETH_withdraw \\ asm_rewrite_tac[])
  \\ rpt (qpat_x_assum `balance_slot_key _ ∉ _`
            (strip_assume_tac o
             REWRITE_RULE [IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM]))
  \\ asm_rewrite_tac[lookup_update_storage, WETH_withdraw_fields,
                     APPLY_UPDATE_THM]
  \\ qpat_assum `n ≤ _` (rewrite_tac o single o GSYM o MATCH_MP n2w_sub)
  \\ rpt gen_tac \\ disch_then (map_every assume_tac o CONJUNCTS)
  \\ Cases_on `src = a` >- (pop_assum SUBST_ALL_TAC \\ rewrite_tac[])
  \\ asm_rewrite_tac[]
  \\ Cases_on `balance_slot_key src = balance_slot_key a`
  >- (
    `a ∉ ws.touched` by metis_tac[]
    \\ `src ∉ ws.touched` by metis_tac[IN_IMAGE]
    \\ `ws.balances src = 0 ∧ ws.balances a = 0` by metis_tac[]
    \\ `n = 0` by decide_tac
    \\ asm_rewrite_tac[SUB_0])
  \\ asm_rewrite_tac[]
  \\ qpat_assum `∀a. _ ∧ _ ⇒ lookup_storage _ st = _` irule
  \\ asm_rewrite_tac[]
QED

(* withdraw(wad) over the WETH_EVM relation: either the caller's balance
   and the locked ether drop by wad, or the transaction reverts and WETH is
   unchanged (safety only, as above); assuming the caller's balance slot
   doesn't collide with a touched account's or with slots 0-2 *)
Theorem WETH_EVM_withdraw_run_transaction:
  WETH_EVM addr ws accounts ∧
  zero_value_call (Collect dd, chainId, prevHashes, blk) accounts tx addr
    (function_selector "withdraw" [Uint 256] ++
     enc (Tuple [Uint 256]) (ListV [NumV wad])) 60000 s ∧
  wad ≤ ws.balances tx.from ∧
  (∀b. b ∈ ws.touched ∧ balance_slot_key b = balance_slot_key tx.from ⇒
       b = tx.from) ∧
  balance_slot_key tx.from ∉ {0w; 1w; 2w} ∧
  ¬fIN tx.from precompile_addresses ∧
  blk.coinBase ≠ addr
  ⇒
  ∃result accounts'.
    run_transaction (Collect dd) F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    (∀a. a ≠ addr ⇒
         (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    ((result.result = NONE ∧
      result.output = [] ∧
      (∃calleeLogs.
         result.logs =
           calleeLogs ++
           [<| logger := addr;
               topics :=
                 [word_of_bytes_be
                    (Keccak_256_string "Withdrawal(address,uint256)");
                  w2w tx.from];
               data := enc (Tuple [Uint 256]) (ListV [NumV wad]) |>]) ∧
      (lookup_account tx.from s.rollback.accounts).balance + wad ≤
        (lookup_account tx.from accounts').balance ∧
      WETH_EVM addr (WETH_withdraw tx.from wad ws) accounts') ∨
     (result.result = SOME Reverted ∧
      result.output = [] ∧
      result.logs = [] ∧
      WETH_EVM addr ws accounts'))
Proof
  strip_tac
  \\ qpat_x_assum `WETH_EVM _ _ _`
       (strip_assume_tac o SIMP_RULE std_ss [WETH_EVM_def, LET_THM])
  \\ qpat_assum `wf_WETH_state ws`
       (strip_assume_tac o REWRITE_RULE [wf_WETH_state_def])
  \\ `lookup_storage (balance_slot_key tx.from)
        (lookup_account addr accounts).storage = n2w (ws.balances tx.from)`
  by (first_assum irule \\ asm_rewrite_tac[] \\ metis_tac[IN_IMAGE])
  \\ `wad ≤ w2n (lookup_storage (balance_slot_key tx.from)
                   (lookup_account addr accounts).storage)`
  by (qpat_assum `lookup_storage (balance_slot_key tx.from) _ = _`
        SUBST1_TAC
      \\ `ws.balances tx.from MOD dimword (:256) = ws.balances tx.from`
      by (irule LESS_MOD
          \\ rewrite_tac[EVAL “dimword (:256)”, GSYM (EVAL “2n ** 256”)]
          \\ qpat_assum `∀a. ws.balances a < _` MATCH_ACCEPT_TAC)
      \\ asm_rewrite_tac[w2n_n2w])
  \\ mp_tac weth_withdraw_run_transaction
  \\ impl_tac >- asm_rewrite_tac[]
  \\ disch_then (qx_choosel_then [`result`, `accounts'`]
       (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)))
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ qpat_x_assum `_ ∨ _` strip_assume_tac
  >- (
    disj1_tac
    \\ conj_tac >- first_assum ACCEPT_TAC
    \\ conj_tac >- first_assum ACCEPT_TAC
    \\ conj_tac >- (qexists_tac `calleeLogs` \\ first_assum ACCEPT_TAC)
    \\ conj_tac >- first_assum ACCEPT_TAC
    \\ rewrite_tac[WETH_EVM_def]
    \\ qpat_x_assum `lookup_account addr accounts' = _` SUBST1_TAC
    \\ simp_tac std_ss [LET_THM]
    \\ mp_tac (Q.INST [`src` |-> `(tx:transaction).from`, `n` |-> `wad`,
                       `st` |-> `(lookup_account addr accounts).storage`]
                      WETH_withdraw_storage)
    \\ impl_tac >- asm_rewrite_tac[]
    \\ simp_tac std_ss [LET_THM] \\ strip_tac
    \\ mp_tac (Q.INST [`src` |-> `(tx:transaction).from`, `n` |-> `wad`,
                       `st` |-> `(lookup_account addr accounts).storage`]
                      WETH_withdraw_allowance_storage)
    \\ impl_tac >- asm_rewrite_tac[]
    \\ strip_tac
    \\ qpat_x_assum `lookup_storage (balance_slot_key tx.from) _ = _` kall_tac
    \\ asm_rewrite_tac[account_state_accfupds, K_THM,
                       CONJUNCT2 (CONJUNCT2 WETH_withdraw_fields)])
  \\ disj2_tac
  \\ asm_rewrite_tac[WETH_EVM_def]
  \\ simp_tac std_ss [LET_THM]
  \\ asm_rewrite_tac[]
QED

(* ---------------------------------------------------------------- *)
(* withdraw reverts when the caller's balance is below wad, or when it is
   sent value *)

(* the balance check at 2521 fails, falling through to the REVERT at
   2595 *)
val withdraw_revert_path =
  [(0, "_skip"), (13, "_skip"), (65, "_skip"), (76, "_skip"), (87, "_skip"),
   (98, "_take"), (579, "_take"), (590, "_Jump"), (2521, "_skip"),
   (2595, "_outermost")]

(* the callvalue check at 579 fails, falling through to the REVERT at
   586 *)
val withdraw_value_revert_path =
  [(0, "_skip"), (13, "_skip"), (65, "_skip"), (76, "_skip"), (87, "_skip"),
   (98, "_take"), (579, "_skip"), (586, "_outermost")]

fun revert_lift path =
  path |> compose_path |> path_reads |> path_keys |> spec_start
  |> spec_code |> spec_pool
  |> spec_ordered ["evm_Exception", "evm_ReturnData", "evm_Contexts",
                   "evm_GasUsed", "evm_MsgParams", "evm_TxParams"]
  |> spec_lift SPEC_to_run_transaction_failure

val withdraw_revert_lift = revert_lift withdraw_revert_path
val withdraw_value_revert_lift = revert_lift withdraw_value_revert_path

Theorem weth_withdraw_revert_run_transaction:
  (lookup_account addr accounts).code = contract_code ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "withdraw" [Uint 256] ++
     enc (Tuple [Uint 256]) (ListV [NumV wad])) 2467 s ∧
  w2n (lookup_storage (balance_slot_key tx.from)
         (lookup_account addr accounts).storage) < wad ∧
  wad < dimword (:256) ∧
  access_slot_check dom (SK addr (balance_slot_key tx.from))
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = SOME Reverted ∧
    result.output = [] ∧
    result.logs = [] ∧
    (∀a. (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    (lookup_account addr accounts').code = contract_code ∧
    (lookup_account addr accounts').storage =
      (lookup_account addr accounts).storage ∧
    (blk.coinBase ≠ addr ⇒
     lookup_account addr accounts' = lookup_account addr accounts)
Proof
  PURE_REWRITE_TAC [withdraw_value_enc, zero_value_call_def]
  \\ strip_tac
  \\ strip_assume_tac contract_code_not_delegation
  \\ drule_all initial_state_call_code \\ strip_tac
  \\ drule initial_state_contract
  \\ disch_then (qspec_then `addr` mp_tac)
  \\ impl_tac >- gvs[]
  \\ strip_tac
  \\ fs[GSYM parsed_contract_code_def]
  \\ drule_all wf_initial_state \\ strip_tac
  \\ `∃rest. tx.data = [0x2Ew; 0x1Aw; 0x7Dw; 0x4Dw] ++
                       word_to_bytes (n2w wad : bytes32) T ++ rest`
  by (qpat_x_assum `_ ≼ tx.data` mp_tac
      \\ rewrite_tac[withdraw_selector_eq, IS_PREFIX_APPEND]
      \\ strip_tac \\ simp[])
  \\ mp_tac (Q.INST [‘p’ |-> ‘ctxt.msgParams’, ‘rb’ |-> ‘s.rollback’,
                     ‘d’ |-> ‘dom’, ‘rd’ |-> ‘[]’, ‘returnCode’ |-> ‘F’,
                     ‘txParams’ |-> ‘s.txParams’, ‘callee’ |-> ‘addr’,
                     ‘s'’ |-> ‘s with rollback updated_by
                       (λr. r with accounts updated_by
                              transfer_value tx.from addr tx.value)’]
                    withdraw_revert_lift)
  \\ impl_tac
  >- (
    simp_tac pure_ss [evm2set_def, GSYM STAR_ASSOC]
    \\ simp[STAR_evm2set, STAR_evm_OriginalAccounts, STAR_CODE_POOL_evm2set,
            cond_STAR, SEP_T_def,
            transfer_value_zero, execution_state_component_equality,
            rollback_state_component_equality, fmap_entries_def,
            SIMP_RULE std_ss [APPEND] withdraw_selector_calldata,
            DROP_APPEND, DROP_LENGTH_TOO_LONG, calldata_word, mask_and_w2w,
            balance_slot_key_bytes]
    \\ qpat_assum `lookup_account addr s.rollback.accounts = _`
         (fn th => rewrite_tac[th])
    \\ gas_bounds_tac
    \\ gvs[])
  \\ strip_tac
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ gvs[lookup_account_pay_transaction_gas, transfer_value_zero]
  \\ rw[account_state_component_equality]
QED

Theorem weth_withdraw_value_revert_run_transaction:
  (lookup_account addr accounts).code = contract_code ∧
  contract_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "withdraw" [Uint 256]) 197 s ∧
  tx.value ≠ 0 ∧ tx.value < dimword (:256)
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = SOME Reverted ∧
    result.output = [] ∧
    result.logs = [] ∧
    (∀a. (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    (lookup_account addr accounts').code = contract_code ∧
    (lookup_account addr accounts').storage =
      (lookup_account addr accounts).storage ∧
    (blk.coinBase ≠ addr ⇒
     lookup_account addr accounts' = lookup_account addr accounts)
Proof
  PURE_REWRITE_TAC [contract_call_def]
  \\ strip_tac
  \\ strip_assume_tac contract_code_not_delegation
  \\ drule_all initial_state_call_code \\ strip_tac
  \\ drule initial_state_contract
  \\ disch_then (qspec_then `addr` mp_tac)
  \\ impl_tac >- gvs[]
  \\ strip_tac
  \\ fs[GSYM parsed_contract_code_def]
  \\ drule_all wf_initial_state \\ strip_tac
  \\ `∃rest. tx.data = [0x2Ew; 0x1Aw; 0x7Dw; 0x4Dw] ++ rest`
  by (qpat_x_assum `_ ≼ tx.data` mp_tac
      \\ rewrite_tac[withdraw_selector_eq, IS_PREFIX_APPEND])
  \\ `tx.from ≠ addr` by gvs[]
  \\ mp_tac (Q.INST [‘p’ |-> ‘ctxt.msgParams’,
                     ‘rb’ |-> ‘s.rollback with accounts updated_by
                                 transfer_value tx.from addr tx.value’,
                     ‘d’ |-> ‘dom’, ‘rd’ |-> ‘[]’, ‘returnCode’ |-> ‘F’,
                     ‘txParams’ |-> ‘s.txParams’, ‘callee’ |-> ‘addr’,
                     ‘s'’ |-> ‘s’,
                     ‘s’ |-> ‘s with rollback updated_by
                       (λr. r with accounts updated_by
                              transfer_value tx.from addr tx.value)’]
                    withdraw_value_revert_lift)
  \\ impl_tac
  >- (
    simp_tac pure_ss [evm2set_def, GSYM STAR_ASSOC]
    \\ simp[STAR_evm2set, STAR_evm_OriginalAccounts, STAR_CODE_POOL_evm2set,
            cond_STAR, SEP_T_def,
            execution_state_component_equality,
            rollback_state_component_equality, fmap_entries_def,
            SIMP_RULE std_ss [APPEND] withdraw_selector_calldata,
            lookup_account_transfer_value_fields,
            lookup_account_transfer_value_to]
    \\ qpat_assum `lookup_account addr s.rollback.accounts = _`
         (fn th => rewrite_tac[th])
    \\ gvs[wf_state_def, all_accounts_def, stack_room_ok_def,
           gas_stack_ok_def, outputTo_consistent_stack_def])
  \\ strip_tac
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ gvs[lookup_account_pay_transaction_gas]
  \\ rw[account_state_component_equality]
QED

(* the two reverts over the WETH_EVM relation, which they preserve *)
Theorem WETH_EVM_withdraw_revert_run_transaction:
  WETH_EVM addr ws accounts ∧
  zero_value_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "withdraw" [Uint 256] ++
     enc (Tuple [Uint 256]) (ListV [NumV wad])) 2467 s ∧
  ws.balances tx.from < wad ∧ wad < dimword (:256) ∧
  (tx.from ∉ ws.touched ⇒
   balance_slot_key tx.from ∉ IMAGE balance_slot_key ws.touched) ∧
  balance_slot_key tx.from ∉ {0w; 1w; 2w} ∧
  access_slot_check dom (SK addr (balance_slot_key tx.from)) ∧
  blk.coinBase ≠ addr
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = SOME Reverted ∧
    result.output = [] ∧
    result.logs = [] ∧
    (∀a. a ≠ addr ⇒
         (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    WETH_EVM addr ws accounts'
Proof
  strip_tac
  \\ `lookup_storage (balance_slot_key tx.from)
        (lookup_account addr accounts).storage = n2w (ws.balances tx.from)`
  by (qpat_x_assum `WETH_EVM _ _ _` mp_tac
      \\ simp_tac std_ss [WETH_EVM_def, LET_THM] \\ strip_tac
      \\ first_x_assum irule \\ gvs[] \\ metis_tac[])
  \\ `ws.balances tx.from < dimword (:256)`
  by (qpat_x_assum `WETH_EVM _ _ _` mp_tac
      \\ simp[WETH_EVM_def, wf_WETH_state_def])
  \\ `w2n (lookup_storage (balance_slot_key tx.from)
             (lookup_account addr accounts).storage) < wad`
  by gvs[]
  \\ `(lookup_account addr accounts).code = contract_code`
  by gvs[WETH_EVM_def]
  \\ drule_all weth_withdraw_revert_run_transaction \\ strip_tac
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ `lookup_account addr accounts' = lookup_account addr accounts` by gvs[]
  \\ rpt conj_tac \\ TRY (first_assum ACCEPT_TAC)
  >- (gen_tac \\ strip_tac \\ asm_rewrite_tac[])
  \\ qpat_x_assum `WETH_EVM _ _ _` mp_tac
  \\ simp_tac std_ss [WETH_EVM_def, LET_THM]
  \\ pop_assum SUBST1_TAC
  \\ asm_rewrite_tac[]
  \\ strip_tac \\ rpt conj_tac \\ first_assum ACCEPT_TAC
QED

Theorem WETH_EVM_withdraw_value_revert_run_transaction:
  WETH_EVM addr ws accounts ∧
  contract_call (dom, chainId, prevHashes, blk) accounts tx addr
    (function_selector "withdraw" [Uint 256]) 197 s ∧
  tx.value ≠ 0 ∧ tx.value < dimword (:256) ∧
  blk.coinBase ≠ addr
  ⇒
  ∃result accounts'.
    run_transaction dom F chainId prevHashes blk accounts tx =
      SOME (result, accounts') ∧
    result.result = SOME Reverted ∧
    result.output = [] ∧
    result.logs = [] ∧
    (∀a. a ≠ addr ⇒
         (lookup_account a accounts').code =
         (lookup_account a s.rollback.accounts).code ∧
         (lookup_account a accounts').storage =
         (lookup_account a s.rollback.accounts).storage ∧
         (lookup_account a accounts').nonce =
         (lookup_account a s.rollback.accounts).nonce) ∧
    WETH_EVM addr ws accounts'
Proof
  strip_tac
  \\ `(lookup_account addr accounts).code = contract_code`
  by gvs[WETH_EVM_def]
  \\ drule_all weth_withdraw_value_revert_run_transaction \\ strip_tac
  \\ qexistsl_tac [`result`, `accounts'`]
  \\ `lookup_account addr accounts' = lookup_account addr accounts` by gvs[]
  \\ rpt conj_tac \\ TRY (first_assum ACCEPT_TAC)
  >- (gen_tac \\ strip_tac \\ asm_rewrite_tac[])
  \\ qpat_x_assum `WETH_EVM _ _ _` mp_tac
  \\ simp_tac std_ss [WETH_EVM_def, LET_THM]
  \\ pop_assum SUBST1_TAC
  \\ asm_rewrite_tac[]
  \\ strip_tac \\ rpt conj_tac \\ first_assum ACCEPT_TAC
QED
