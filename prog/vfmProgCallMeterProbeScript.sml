Theory vfmProgCallMeterProbe
Ancestors vfmExecution vfmContext vfmConstants vfmState arithmetic

(* Independent validation of the no-spill CALL charge/refill interface.
   No dependency on the unfinished SPEC rules. *)
Theorem call_creation_charge_refill[local]:
  s.contexts = (c,k)::cs /\
  (if charged then new_account_state_gas else 0) <= c.stateGasLeft ==>
  (do charge_new_account charged; credit_new_account charged od) s =
  (INL (), s with contexts :=
    (c with <|gasUsed := c.gasUsed -
                 MIN (if charged then new_account_state_gas else 0) c.stateGasSpilled;
              stateGasSpilled := c.stateGasSpilled -
                 MIN (if charged then new_account_state_gas else 0) c.stateGasSpilled;
              stateGasLeft := c.stateGasLeft -
                 MIN (if charged then new_account_state_gas else 0) c.stateGasSpilled|>,k)::cs)
Proof
  strip_tac >> Cases_on `charged` >> gvs[] >>
  simp[charge_new_account_def, credit_new_account_def,
       charge_state_gas_def, credit_state_gas_refund_def,
       bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def, LET_THM,
       context_component_equality, execution_state_component_equality] >>
  simp[MIN_DEF] >> rw[] >> decide_tac
QED

Theorem positive_spill_refill_probe[local]:
  let c = (ctx:context) with <|gasUsed := 200000; stateGasLeft := 183600;
                     stateGasSpilled := 7|>;
      s = initial with contexts := [(c,k)]
  in (do charge_new_account T; credit_new_account T od) s =
     (INL (), s with contexts :=
        [(c with <|gasUsed := 199993; stateGasLeft := 183593;
                   stateGasSpilled := 0|>,k)])
Proof
  simp[LET_THM, charge_new_account_def, credit_new_account_def,
       charge_state_gas_def, credit_state_gas_refund_def,
       bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def, new_account_state_gas_def,
       cost_per_state_byte_def, state_bytes_per_new_account_def]
QED
