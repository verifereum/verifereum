Theory vfmCallBudget
Ancestors vfmCallMeterBase vfmContext vfmState vfmTypes arithmetic list

(* The accumulator is the total claim of descendants above this frame. *)
Definition call_meter_chain_def:
  (call_meter_chain above [] <=> T) /\
  (call_meter_chain above (c::cs) <=>
    c.stateGasSpilled + c.stateGasCommitted + above <= c.gasUsed /\
    call_meter_chain (above + call_meter_claim c) cs)
End

Definition call_meter_total_def:
  call_meter_total cs = SUM (MAP call_meter_claim cs)
End

Definition call_meter_prefix_def:
  call_meter_prefix n s =
    TAKE (LENGTH s.contexts - n + 1) (MAP FST s.contexts)
End

Definition call_meter_budget_def:
  call_meter_budget n grant s <=> LENGTH s.contexts < n \/
    (call_meter_total (call_meter_prefix n s) <= grant /\
     call_meter_chain 0 (call_meter_prefix n s))
End

Theorem call_meter_chain_mono:
  !cs a b. call_meter_chain a cs /\ b <= a ==> call_meter_chain b cs
Proof
  Induct >> simp[call_meter_chain_def] >> rpt strip_tac >>
  first_x_assum irule >> qexists `a + call_meter_claim h` >> simp[]
QED

Theorem call_meter_chain_indexed:
  !cs above. call_meter_chain above cs <=>
    !i. i < LENGTH cs ==>
      (EL i cs).stateGasSpilled + (EL i cs).stateGasCommitted + above +
        call_meter_total (TAKE i cs) <= (EL i cs).gasUsed
Proof
  Induct >- simp[call_meter_chain_def] >>
  rpt gen_tac >> simp[call_meter_chain_def] >> eq_tac
  >- (strip_tac >> Cases >> simp[call_meter_total_def] >>
      rpt strip_tac >> first_x_assum drule >> simp[call_meter_total_def] >> decide_tac) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[call_meter_total_def]) >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[call_meter_total_def] >> decide_tac
QED

Theorem call_meter_total_cons[simp]:
  call_meter_total (c::cs) = call_meter_claim c + call_meter_total cs
Proof
  simp[call_meter_total_def]
QED

Theorem call_meter_total_nil[simp]:
  call_meter_total [] = 0
Proof
  simp[call_meter_total_def]
QED

(* Local replacement contracts deliberately separate top backing from the
   currency passed to ancestors. No ancestor's fields need to be unfolded. *)
Theorem call_meter_chain_replace:
  call_meter_chain 0 (c::cs) /\ call_meter_backed d /\
  call_meter_claim d <= call_meter_claim c ==>
  call_meter_chain 0 (d::cs)
Proof
  simp[call_meter_chain_def, call_meter_backed_def] >> rpt strip_tac >>
  drule call_meter_chain_mono >> disch_then irule >> simp[]
QED

Theorem call_meter_list_replace:
  call_meter_total (c::cs) <= grant /\ call_meter_chain 0 (c::cs) /\
  call_meter_backed d /\ call_meter_claim d <= call_meter_claim c ==>
  call_meter_total (d::cs) <= grant /\ call_meter_chain 0 (d::cs)
Proof
  rpt strip_tac
  >- (gvs[] >> decide_tac) >>
  irule call_meter_chain_replace >> metis_tac[]
QED

Theorem call_meter_list_push:
  call_meter_total (c::cs) <= grant /\ call_meter_chain 0 (c::cs) /\
  call_meter_backed child /\
  parent.stateGasSpilled + parent.stateGasCommitted + call_meter_claim child <=
    parent.gasUsed /\
  call_meter_claim child + call_meter_claim parent <= call_meter_claim c ==>
  call_meter_total (child::parent::cs) <= grant /\
  call_meter_chain 0 (child::parent::cs)
Proof
  simp[call_meter_chain_def, call_meter_backed_def] >> rpt strip_tac >>
  drule call_meter_chain_mono >> disch_then irule >> decide_tac
QED

Theorem call_meter_list_pop:
  call_meter_total (child::parent::cs) <= grant /\
  call_meter_chain 0 (child::parent::cs) /\ call_meter_backed merged /\
  call_meter_claim merged <= call_meter_claim child + call_meter_claim parent ==>
  call_meter_total (merged::cs) <= grant /\ call_meter_chain 0 (merged::cs)
Proof
  simp[call_meter_chain_def, call_meter_backed_def] >> rpt strip_tac >>
  drule call_meter_chain_mono >> disch_then irule >> decide_tac
QED

Theorem call_meter_budget_exit:
  LENGTH s.contexts < n ==> call_meter_budget n grant s
Proof
  simp[call_meter_budget_def]
QED

Theorem call_meter_prefix_entry:
  s.contexts = (c,rb)::rest ==>
  call_meter_prefix (LENGTH rest + 1) s = [c]
Proof
  simp[call_meter_prefix_def]
QED

Theorem call_meter_budget_fresh:
  s.contexts =
    (initial_context callee code static output charged sg tx,rb)::(caller,cb)::rest ==>
  call_meter_budget (LENGTH rest + 2) tx.gasLimit s
Proof
  strip_tac >>
  `SUC (SUC (LENGTH rest)) = LENGTH rest + 2` by decide_tac >>
  simp[call_meter_budget_def, call_meter_prefix_def, call_meter_chain_def,
       call_meter_initial_claim] >> simp[initial_context_def]
QED

Theorem call_meter_budget_top:
  call_meter_budget n grant s /\ n <= LENGTH s.contexts /\
  s.contexts = (c,rb)::rest /\ 0 < n ==>
  call_meter_backed c
Proof
  simp[call_meter_budget_def, call_meter_prefix_def] >> rpt strip_tac >>
  `LENGTH rest + 1 - n + 1 = SUC (LENGTH rest + 1 - n)` by decide_tac >>
  gvs[call_meter_chain_def, call_meter_backed_def]
QED

Theorem call_meter_budget_root_claim:
  call_meter_budget n grant s /\ LENGTH s.contexts = n /\
  s.contexts = (c,rb)::rest ==>
  call_meter_claim c <= grant
Proof
  simp[call_meter_budget_def, call_meter_prefix_def] >> rpt strip_tac >> gvs[]
QED

Theorem call_meter_prefix_cons:
  s.contexts = (c,rb)::rest /\ n <= LENGTH rest + 1 ==>
  call_meter_prefix n s = c::TAKE (LENGTH rest + 1 - n) (MAP FST rest)
Proof
  rpt strip_tac >>
  `SUC (LENGTH rest) - n + 1 = SUC (LENGTH rest + 1 - n)` by decide_tac >>
  simp[call_meter_prefix_def]
QED

Theorem call_meter_budget_replace:
  call_meter_budget n grant s /\ n <= LENGTH s.contexts /\
  s.contexts = (c,rb)::rest /\ t.contexts = (d,db)::rest /\
  call_meter_backed d /\ call_meter_claim d <= call_meter_claim c ==>
  call_meter_budget n grant t
Proof
  rpt strip_tac >>
  `n <= LENGTH rest + 1` by gvs[] >>
  `call_meter_prefix n s = c::TAKE (LENGTH rest + 1 - n) (MAP FST rest)` by
    (irule call_meter_prefix_cons >> simp[]) >>
  `call_meter_prefix n t = d::TAKE (LENGTH rest + 1 - n) (MAP FST rest)` by
    (irule call_meter_prefix_cons >> simp[]) >>
  gvs[call_meter_budget_def, Excl "call_meter_total_cons"] >>
  irule call_meter_list_replace >> metis_tac[]
QED

Theorem call_meter_budget_push:
  call_meter_budget n grant s /\ n <= LENGTH s.contexts /\
  s.contexts = (c,rb)::rest /\
  t.contexts = (child,crb)::(parent,prb)::rest /\
  call_meter_backed child /\
  parent.stateGasSpilled + parent.stateGasCommitted + call_meter_claim child <=
    parent.gasUsed /\
  call_meter_claim child + call_meter_claim parent <= call_meter_claim c ==>
  call_meter_budget n grant t
Proof
  rpt strip_tac >>
  `n <= LENGTH rest + 1` by gvs[] >>
  `call_meter_prefix n s = c::TAKE (LENGTH rest + 1 - n) (MAP FST rest)` by
    (irule call_meter_prefix_cons >> simp[]) >>
  `SUC (SUC (LENGTH rest)) - n + 1 = SUC (SUC (LENGTH rest + 1 - n))`
    by decide_tac >>
  gvs[call_meter_budget_def, call_meter_prefix_def, Excl "call_meter_total_cons"] >>
  irule call_meter_list_push >> simp[AC ADD_ASSOC ADD_COMM] >>
  qexists `c` >> gvs[]
QED

(* Internal pop retains the root. At root exit there is intentionally no
   constraint on the newly exposed external caller. *)
Theorem call_meter_budget_pop:
  call_meter_budget n grant s /\ n < LENGTH s.contexts /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  t.contexts = (merged,mrb)::rest /\ call_meter_backed merged /\
  call_meter_claim merged <= call_meter_claim child + call_meter_claim parent ==>
  call_meter_budget n grant t
Proof
  rpt strip_tac >>
  `n <= LENGTH rest + 1` by gvs[] >>
  `call_meter_prefix n t = merged::TAKE (LENGTH rest + 1 - n) (MAP FST rest)` by
    (irule call_meter_prefix_cons >> simp[]) >>
  `SUC (SUC (LENGTH rest)) - n + 1 = SUC (SUC (LENGTH rest + 1 - n))`
    by decide_tac >>
  gvs[call_meter_budget_def, call_meter_prefix_def, Excl "call_meter_total_cons"] >>
  irule call_meter_list_pop >> metis_tac[]
QED

Theorem call_meter_budget_root_exit:
  LENGTH s.contexts = n /\ LENGTH t.contexts + 1 = LENGTH s.contexts ==>
  call_meter_budget n grant t
Proof
  rpt strip_tac >> irule call_meter_budget_exit >> decide_tac
QED

Theorem call_meter_budget_root_refund:
  call_meter_budget n grant s /\ LENGTH s.contexts = n /\
  s.contexts = (c,rb)::rest ==>
  c.msgParams.gasLimit - c.gasUsed <= grant
Proof
  rpt strip_tac >> drule_all call_meter_budget_root_claim >>
  simp[call_meter_claim_def]
QED

Theorem call_meter_budget_indexed:
  call_meter_budget n grant s <=> LENGTH s.contexts < n \/
    (call_meter_total (call_meter_prefix n s) <= grant /\
     !i. i < LENGTH (call_meter_prefix n s) ==>
       (EL i (call_meter_prefix n s)).stateGasSpilled +
       (EL i (call_meter_prefix n s)).stateGasCommitted +
       call_meter_total (TAKE i (call_meter_prefix n s)) <=
       (EL i (call_meter_prefix n s)).gasUsed)
Proof
  simp[call_meter_budget_def, call_meter_chain_indexed]
QED

Theorem call_meter_budget_parent_margin:
  call_meter_budget n grant s /\ n < LENGTH s.contexts /\
  s.contexts = (child,crb)::(parent,prb)::rest ==>
  parent.stateGasSpilled + parent.stateGasCommitted + call_meter_claim child <=
    parent.gasUsed
Proof
  rpt strip_tac >>
  `SUC (SUC (LENGTH rest)) - n + 1 = SUC (SUC (LENGTH rest + 1 - n))`
    by (gvs[] >> decide_tac) >>
  gvs[call_meter_budget_def, call_meter_prefix_def, call_meter_chain_def]
QED

(* A settled successful child exercises the actual absorb/repay expression.
   This is a list-interface test, not yet a theorem about handler execution. *)
Theorem call_meter_list_settled_pop:
  call_meter_total (child::parent::cs) <= grant /\
  call_meter_chain 0 (child::parent::cs) /\
  parent.gasUsed <= parent.msgParams.gasLimit ==>
  let merged = repay_state_gas_spill_context
    (absorb_state_gas
      (parent with gasUsed := parent.gasUsed -
        (child.msgParams.gasLimit - child.gasUsed))
      child.stateGasLeft child.stateGasSpilled child.stateGasCommitted)
  in call_meter_total (merged::cs) <= grant /\ call_meter_chain 0 (merged::cs)
Proof
  strip_tac >> simp[LET_THM, Excl "call_meter_total_cons"] >>
  irule call_meter_list_pop >>
  `parent.stateGasSpilled + parent.stateGasCommitted + call_meter_claim child <=
    parent.gasUsed` by gvs[call_meter_chain_def] >>
  conj_tac
  >- (irule call_meter_success_pop_backed >> gvs[call_meter_claim_def]) >>
  qexistsl [`child`, `parent`] >> simp[] >>
  drule_all call_meter_success_pop_claim >> simp[]
QED
