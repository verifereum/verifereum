Theory vfmProgCallPrefixProbe
Ancestors vfmExecution vfmExecutionProp vfmContext vfmConstants vfmState
  vfmTypes vfmBuffer words list arithmetic finite_map

(* Mirrors the existing prog boundary definitions for independent validation. *)
Definition msdomain_add_def:
  msdomain_add a d =
  case d of Enforce _ => d
          | Collect x => Collect $ x with addresses updated_by fINSERT a
End
Definition accesses_add_def:
  accesses_add a rb = rb with accesses updated_by
    (\x. x with addresses updated_by fINSERT a)
End
Definition access_cost_def:
  access_cost rb a =
  if fIN a rb.accesses.addresses then warm_access_cost else cold_access_cost
End
Definition access_check_def:
  access_check d a =
  case d of Enforce x => fIN a x.addresses | Collect _ => T
End
Definition delegate_check_def:
  delegate_check c d rb dCost newRb newDom <=>
  case get_delegate c of
    NONE => dCost = 0 /\ newRb = rb /\ newDom = d
  | SOME delegate => access_check d delegate /\
      dCost = access_cost rb delegate /\
      newRb = accesses_add delegate rb /\ newDom = msdomain_add delegate d
End
Theorem access_address_split[local]:
  access_check s.msdomain a ==>
  access_address a s =
  (INL (access_cost s.rollback a),
   s with <|rollback updated_by accesses_add a;
            msdomain updated_by msdomain_add a|>)
Proof
  simp[access_address_def, domain_check_def] >>
  Cases_on `s.msdomain` >>
  simp[access_check_def, return_def, bind_def, ignore_bind_def,
       access_cost_def, set_domain_def, msdomain_add_def,
       accesses_add_def, access_sets_component_equality,
       execution_state_component_equality, rollback_state_component_equality]
QED

Theorem call_delegate_segment[local]:
  s.rollback = rb /\ s.msdomain = d /\
  delegate_check code d rb cost rb' d' ==>
  (case get_delegate code of
     NONE => return (code,0)
   | SOME del => do
       n <- access_address del;
       return ((lookup_account del rb.accounts).code,n)
     od) s =
  (INL ((case get_delegate code of NONE => code
           | SOME del => (lookup_account del rb.accounts).code),cost),
   s with <|rollback := rb'; msdomain := d'|>)
Proof
  strip_tac >> Cases_on `get_delegate code` >>
  gvs[delegate_check_def, return_def, bind_def, access_address_split,
      execution_state_component_equality]
QED

Theorem call_access_segment[local]:
  s.rollback = rb /\ s.msdomain = d /\ access_check d addr /\
  delegate_check (lookup_account addr rb.accounts).code
    (msdomain_add addr d) (accesses_add addr rb) dCost newRb newDom ==>
  (do
     aCost <- access_address addr;
     accounts <- get_accounts;
     pair <- (case get_delegate (lookup_account addr accounts).code of
       NONE => return ((lookup_account addr accounts).code,0)
     | SOME del => do
         n <- access_address del;
         return ((lookup_account del accounts).code,n)
       od);
     return (aCost,accounts,pair)
   od) s =
  (INL (access_cost rb addr, rb.accounts,
    ((case get_delegate (lookup_account addr rb.accounts).code of
        NONE => (lookup_account addr rb.accounts).code
      | SOME del => (lookup_account del rb.accounts).code),dCost)),
   s with <|rollback := newRb; msdomain := newDom|>)
Proof
  strip_tac >>
  simp[Once bind_def, access_address_split] >>
  simp[get_accounts_def, bind_def, return_def, accesses_add_def] >>
  Cases_on `get_delegate (lookup_account addr rb.accounts).code` >>
  gvs[delegate_check_def, access_address_split, bind_def, return_def,
      execution_state_component_equality]
QED

Theorem charge_new_account_apply[local]:
  s.contexts <> [] /\
  (if charged then new_account_state_gas else 0) <=
    (FST (HD s.contexts)).stateGasLeft ==>
  charge_new_account charged s =
    (INL (), s with contexts :=
      (FST (HD s.contexts) with
         stateGasLeft := (FST (HD s.contexts)).stateGasLeft -
                         (if charged then new_account_state_gas else 0),
       SND (HD s.contexts)) :: TL s.contexts)
Proof
  strip_tac >> Cases_on `s.contexts` >- gvs[] >>
  rename1 `s.contexts = h::ts` >> Cases_on `h` >>
  Cases_on `charged` >>
  gvs[charge_new_account_def, charge_state_gas_def, bind_def,
      get_current_context_def, set_current_context_def, return_def,
      assert_def, context_component_equality,
      execution_state_component_equality]
QED


Theorem call_consume_gas_apply[local]:
  s.contexts = (c,k)::cs /\ c.gasUsed + n <= c.msgParams.gasLimit ==>
  consume_gas n s =
  (INL (), s with contexts := (c with gasUsed := c.gasUsed + n,k)::cs)
Proof
  strip_tac >>
  `n + c.gasUsed <= c.msgParams.gasLimit` by decide_tac >>
  simp[consume_gas_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, ADD_COMM]
QED

Theorem call_static_assert_apply[local]:
  s.contexts = (c,k)::cs /\ (doStatic ==> ~c.msgParams.static) ==>
  (if doStatic then assert_not_static else return ()) s = (INL (),s)
Proof
  strip_tac >> Cases_on `doStatic` >>
  gvs[assert_not_static_def, get_static_def, get_current_context_def,
      bind_def, return_def, assert_def]
QED

Theorem call_expand_memory_apply[local]:
  s.contexts = (c,k)::cs ==>
  expand_memory n s =
  (INL (), s with contexts := (c with memory := buffer_extend n c.memory,k)::cs)
Proof
  strip_tac >> simp[expand_memory_def, get_current_context_def,
    set_current_context_def, bind_def, return_def]
QED

Theorem call_get_gas_left_apply[local]:
  s.contexts = (c,k)::cs ==>
  get_gas_left s = (INL (c.msgParams.gasLimit - c.gasUsed),s)
Proof
  strip_tac >> simp[get_gas_left_def, get_current_context_def, bind_def, return_def]
QED

Theorem call_get_callee_apply[local]:
  s.contexts = (c,k)::cs ==>
  get_callee s = (INL c.msgParams.callee,s)
Proof
  strip_tac >> simp[get_callee_def, get_current_context_def, bind_def, return_def]
QED

Theorem call_meter_segment[local]:
  s.contexts = (c,k)::cs /\
  c.gasUsed + baseCost <= c.msgParams.gasLimit /\
  c.gasUsed + baseCost + dynamicGas <= c.msgParams.gasLimit /\
  (if charged then new_account_state_gas else 0) <= c.stateGasLeft /\
  (doStatic ==> ~c.msgParams.static) /\
  call_gas value gas (c.msgParams.gasLimit - (c.gasUsed + baseCost)) 0 0 =
    (dynamicGas,stipend) ==>
  (do
     consume_gas baseCost;
     charge_new_account charged;
     if doStatic then assert_not_static else return ();
     expand_memory expandBy;
     left <- get_gas_left;
     pair <<- call_gas value gas left 0 0;
     consume_gas (FST pair);
     sender <- get_callee;
     return (sender,SND pair)
   od) s =
  (INL (c.msgParams.callee,stipend), s with contexts :=
    (c with <|gasUsed := c.gasUsed + baseCost + dynamicGas;
              memory := buffer_extend expandBy c.memory;
              stateGasLeft := c.stateGasLeft -
                (if charged then new_account_state_gas else 0)|>,k)::cs)
Proof
  strip_tac >>
  `consume_gas baseCost s =
    (INL (), s with contexts :=
      (c with gasUsed := c.gasUsed + baseCost,k)::cs)` by
    (irule call_consume_gas_apply >> simp[]) >>
  simp[bind_def, ignore_bind_def, charge_new_account_apply] >>
  qmatch_goalsub_abbrev_tac `(if doStatic then assert_not_static else return ()) st` >>
  `(if doStatic then assert_not_static else return ()) st = (INL (),st)` by
    (irule call_static_assert_apply >> simp[Abbr `st`]) >>
  simp[] >>
  qabbrev_tac `c1 = FST (HD st.contexts)` >>
  `st.contexts = (c1,k)::cs` by simp[Abbr `st`, Abbr `c1`] >>
  `expand_memory expandBy st =
    (INL (),st with contexts :=
      (c1 with memory := buffer_extend expandBy c1.memory,k)::cs)` by
    (irule call_expand_memory_apply >> simp[]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `get_gas_left st2` >>
  `get_gas_left st2 =
    (INL (c.msgParams.gasLimit - (c.gasUsed + baseCost)),st2)` by
    (`st2.contexts = (c1 with memory := buffer_extend expandBy c1.memory,k)::cs`
       by simp[Abbr `st2`] >>
     drule call_get_gas_left_apply >>
     simp[Abbr `c1`, Abbr `st`, ADD_COMM]) >>
  simp[] >>
  `call_gas value gas (c.msgParams.gasLimit - (baseCost + c.gasUsed)) 0 0 =
    (dynamicGas,stipend)` by metis_tac[ADD_COMM] >>
  simp[] >>
  qabbrev_tac `c2 = FST (HD st2.contexts)` >>
  `consume_gas dynamicGas st2 =
    (INL (),st2 with contexts :=
      (c2 with gasUsed := c2.gasUsed + dynamicGas,k)::cs)` by
    (irule call_consume_gas_apply >>
     simp[Abbr `c2`, Abbr `st2`, Abbr `c1`, Abbr `st`] >> decide_tac) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `get_callee st3` >>
  `get_callee st3 = (INL c.msgParams.callee,st3)` by
    (`st3.contexts =
       (c2 with gasUsed := c2.gasUsed + dynamicGas,k)::cs`
       by simp[Abbr `st3`] >>
     drule call_get_callee_apply >>
     simp[Abbr `c2`, Abbr `st2`, Abbr `c1`, Abbr `st`]) >>
  simp[return_def, Abbr `st3`, Abbr `c2`, Abbr `st2`, Abbr `c1`, Abbr `st`]
QED

Theorem call_pop_stack_apply[local]:
  s.contexts = (c,k)::cs /\ n <= LENGTH c.stack ==>
  pop_stack n s =
  (INL (TAKE n c.stack),s with contexts :=
    (c with stack := DROP n c.stack,k)::cs)
Proof
  strip_tac >> simp[pop_stack_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, assert_def, return_def]
QED

Definition memory_cost_def:
  memory_cost (m:buffer) offset size =
    memory_expansion_cost (buffer_length m)
      (if 0 < size then word_size (offset + size) * 32 else 0)
End
Definition memory_expand_by_def:
  memory_expand_by (m:buffer) offset size =
    MAX (buffer_length m) (if 0 < size then word_size (offset + size) * 32 else 0)
      - buffer_length m
End
Definition expanded_memory_def:
  expanded_memory (m:buffer) offset size =
    buffer_extend (memory_expand_by m offset size) m
End
Theorem memory_expansion_info_split[local]:
  s.contexts <> [] ==>
  memory_expansion_info offset sz s =
  (INL <|cost := memory_cost (FST (HD s.contexts)).memory offset sz;
          expand_by := memory_expand_by (FST (HD s.contexts)).memory offset sz|>,s)
Proof
  rw[memory_expansion_info_def, bind_def, ignore_bind_def,
     get_current_context_def, return_def, memory_cost_def, memory_expand_by_def]
QED

Theorem call_pair_apply[local]:
  !f p. (\(a,b). f a b) p = f (FST p) (SND p)
Proof
  rpt gen_tac >> Cases_on `p` >> simp[]
QED

Theorem call_pair_function[local]:
  (\(a,b). f a b) = (\p. f (FST p) (SND p))
Proof
  simp_tac bool_ss [FUN_EQ_THM, call_pair_apply]
QED

Theorem step_call_segments[local]:
  step_call op = do
    valueOffset <<- if call_has_value op then 1 else 0;
    args <- pop_stack (6 + valueOffset);
    gas <<- w2n $ EL 0 args;
    address <<- w2w $ EL 1 args;
    value <<- if 0 < valueOffset then w2n $ EL 2 args else 0;
    argsOffset <<- w2n $ EL (2 + valueOffset) args;
    argsSize <<- w2n $ EL (3 + valueOffset) args;
    retOffset <<- w2n $ EL (4 + valueOffset) args;
    retSize <<- w2n $ EL (5 + valueOffset) args;
    (offset,size) <<- max_expansion_range
      (argsOffset,argsSize) (retOffset,retSize);
    mx <- memory_expansion_info offset size;
    (accessCost,accounts,(code,delegateCost)) <- (do
      aCost <- access_address address;
      accts <- get_accounts;
      pair <- (case get_delegate (lookup_account address accts).code of
        NONE => return ((lookup_account address accts).code,0)
      | SOME del => do
          n <- access_address del;
          return ((lookup_account del accts).code,n)
        od);
      return (aCost,accts,pair)
    od);
    toAccount <<- lookup_account address accounts;
    charged <<- op = Call /\ 0 < value /\ account_empty toAccount;
    (sender,stipend) <- (do
      consume_gas (static_gas op + accessCost +
        (if 0 < value then call_value_cost else 0) + delegateCost + mx.cost);
      charge_new_account charged;
      if op = Call /\ 0 < value then assert_not_static else return ();
      expand_memory mx.expand_by;
      left <- get_gas_left;
      pair <<- call_gas value gas left 0 0;
      consume_gas (FST pair);
      sender <- get_callee;
      return (sender,SND pair)
    od);
    if (lookup_account sender accounts).balance < value then do
      credit_new_account charged;
      abort_call_value stipend
    od else do
      set_return_data [];
      sucDepth <- get_num_contexts;
      if sucDepth > 1024 then do
        credit_new_account charged;
        abort_unuse stipend
      od else proceed_call op sender address value argsOffset argsSize code stipend
        (Memory <|offset := retOffset; size := retSize|>)
    od
  od
Proof
  simp_tac pure_ss [step_call_def, LET_THM, ignore_bind_def, bind_assoc,
    return_bind, call_pair_function, call_pair_apply, pairTheory.FST, pairTheory.SND] >>
  BETA_TAC >> simp_tac pure_ss [pairTheory.FST, pairTheory.SND] >> REFL_TAC
QED

