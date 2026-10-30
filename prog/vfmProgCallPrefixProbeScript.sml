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
