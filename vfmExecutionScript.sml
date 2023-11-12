open HolKernel boolLib bossLib Parse
     vfmTypesTheory vfmContextTheory;

val _ = new_theory"vfmExecution";

Datatype:
  outcome =
  | OutOfGas
  | Improper
  | Reverted (byte list)
  | Finished (byte list) (event list)
End

Datatype:
  transaction_result =
  | Step transaction_state
  | Done outcome evm_accounts
End

Definition finish_context_def:
  finish_context returnData s =
  if s.contexts = [] then
    Done Improper s.accounts
  else if LENGTH s.contexts = 1 then
    Done (Finished returnData (HD s.contexts).logs) s.accounts
  else
    let callee = HD s.contexts in
    let contexts = TL s.contexts in
    let caller = HD contexts in
    let newCaller = caller with
      <| returnData := returnData
       ; logs       := caller.logs ++ callee.logs
       (* TODO: figure out gasUsed and gasLeft *)
       |> in
    let newContexts = newCaller :: (TL contexts) in
    Step (s with contexts := newContexts)
End

Definition step_inst_def:
    step_inst s Stop = finish_context [] s
  ∧ step_inst s _ = Step s (* TODO *)
End

Definition step_def:
  step s =
  if s.contexts = [] then Done Improper s.accounts else
  let ctx = HD s.contexts in
  let code = (s.accounts (ctx.callParams.callee)).code in
  if ctx.pc < LENGTH code ∧
     IS_SOME (parse_opcode (DROP ctx.pc code))
  then step_inst s (THE (parse_opcode (DROP ctx.pc code)))
  else Done Improper s.accounts
End

val _ = export_theory();
