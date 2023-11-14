open HolKernel boolLib bossLib Parse
     vfmTypesTheory vfmContextTheory;

val _ = new_theory"vfmExecution";

Datatype:
  exception =
  | OutOfGas
  | StackOverflow
  | StackUnderflow
  | InvalidOpcode
  | InvalidJumpDest
  | StackDepthLimit
  | WriteInStaticContext
  | OutOfBoundsRead
  | InvalidParameter
  | InvalidContractPrefix
  | AddressCollision
  | Impossible
End

Datatype:
  outcome =
  | Excepted exception
  | Reverted (byte list)
  | Finished (byte list) (event list) num
End

Datatype:
  transaction_result =
  | Step α transaction_state
  | Done outcome evm_accounts
End

(* TODO: use a monad from the library? *)
Definition bind_def:
  bind r f =
  case r of Done z a => Done z a
          | Step x s => f x s
End

Definition ignore_bind_def:
  ignore_bind r f = bind r (λx s. f s)
End

(* TODO: use byteTheory after moving it to HOL *)
Definition set_byte_def:
  set_byte w i b =
      word_slice 256 ((SUC i) * 8) w ||
      w2w b << i ||
      word_slice (i * 8) 0 w
End

Definition write_memory_def:
    write_memory byteIndex [] memory = memory
  ∧ write_memory byteIndex (byte::bytes) memory =
      let wordIndex = byteIndex DIV 32 in
      let word = case FLOOKUP memory wordIndex of SOME w => w | NONE => 0w in
      let newWord = set_byte word (byteIndex MOD 32) byte in
      write_memory (SUC byteIndex) bytes (FUPDATE memory (wordIndex, newWord))
End

Definition get_current_context_def:
  get_current_context s =
  if s.contexts = [] then
    Done (Excepted Impossible) s.accounts
  else
    Step (HD s.contexts) s
End

Definition set_current_context_def:
  set_current_context s c =
  if s.contexts = [] then
    Done (Excepted Impossible) s.accounts
  else
    Step () (s with contexts := c::(TL s.contexts))
End

Definition finish_context_def:
  finish_context success returnData returnOffset returnSize s =
  if s.contexts = [] then
    Done (Excepted Impossible) s.accounts
  else if LENGTH s.contexts = 1 then
    let context = HD s.contexts in
    Done (Finished returnData context.logs context.gasRefund) s.accounts
  else
    let callee = HD s.contexts in
    let contexts = TL s.contexts in
    let caller = HD contexts in
    let newCaller = caller with
      <| returnData := returnData
       ; logs       := caller.logs ++ callee.logs
       ; gasRefund  := caller.gasRefund + callee.gasRefund
       ; gasUsed    := caller.gasUsed + callee.gasUsed
       (* TODO: revert if out of gas? or should this have been already detected? *)
       ; pc         := caller.pc + 1
       ; stack      := (if success then 1w else 0w) :: caller.stack
       ; memory     :=
           write_memory returnOffset (TAKE returnSize returnData) caller.memory
       |> in
    let newContexts = newCaller :: (TL contexts) in
    Step () (s with contexts := newContexts)
End

Definition consume_gas_def:
  consume_gas n s =
    bind (get_current_context s)
    (λcontext s.
      let newContext = context with gasUsed := context.gasUsed + n in
      if newContext.gasUsed ≤ newContext.callParams.gasLimit
      then set_current_context s newContext
      else Done (Excepted OutOfGas) s.accounts)
End

Definition stack_op_def:
  stack_op n f s =
  bind (get_current_context s)
  (λcontext s.
   if n ≤ LENGTH context.stack
   then
     let newStack = f (TAKE n context.stack) :: DROP n context.stack in
     set_current_context s (context with stack := newStack)
   else Done (Excepted StackUnderflow) s.accounts)
End

Definition step_inst_def:
    step_inst s Stop = finish_context T [] 0 0 s
  ∧ step_inst s Add =
      ignore_bind (consume_gas (static_gas Add) s)
           (stack_op 2 (λl. word_add (EL 0 l) (EL 1 l)))
  ∧ step_inst s Mul =
      ignore_bind (consume_gas (static_gas Add) s)
           (stack_op 2 (λl. word_mul (EL 0 l) (EL 1 l)))
  ∧ step_inst s Sub =
      ignore_bind (consume_gas (static_gas Add) s)
           (stack_op 2 (λl. word_sub (EL 0 l) (EL 1 l)))
  ∧ step_inst s _ = Step () s (* TODO *)
End

Definition step_def:
  step s =
  if s.contexts = [] then Done (Excepted Impossible) s.accounts else
  let ctx = HD s.contexts in
  let code = (s.accounts (ctx.callParams.callee)).code in
  if ctx.pc < LENGTH code then
  if IS_SOME (parse_opcode (DROP ctx.pc code)) then
    step_inst s (THE (parse_opcode (DROP ctx.pc code)))
  else Done (Excepted InvalidOpcode) s.accounts
  else Done (Excepted Impossible) s.accounts
End

val _ = export_theory();
