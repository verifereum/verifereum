open HolKernel boolLib bossLib Parse
     vfmTypesTheory vfmContextTheory;

val _ = new_theory"vfmExecution";

Definition step_inst_def:
  step_inst s i = s (* TODO *)
End

Definition step_def:
  step s =
  if s.contexts = [] then s else
  let ctx = HD s.contexts in
  let code = (s.accounts (ctx.callParams.callee)).code in
  if ctx.pc ≥ LENGTH code then s else
  step_inst s (EL ctx.pc code)
End

val _ = export_theory();
