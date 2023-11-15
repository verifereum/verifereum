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
  set_current_context c s =
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
      then set_current_context newContext s
      else Done (Excepted OutOfGas) s.accounts)
End

Definition stack_op_def:
  stack_op n f s =
  bind (get_current_context s)
  (λcontext s.
   if n ≤ LENGTH context.stack
   then
     let newStack = f (TAKE n context.stack) :: DROP n context.stack in
     set_current_context (context with stack := newStack) s
   else Done (Excepted StackUnderflow) s.accounts)
End

Definition monop_def:
  monop op f s =
    ignore_bind (consume_gas (static_gas op) s)
      (stack_op 1 (λl. f (EL 0 l)))
End

Definition binop_def:
  binop op f s =
    ignore_bind (consume_gas (static_gas op) s)
      (stack_op 2 (λl. f (EL 0 l) (EL 1 l)))
End

Definition with_zero_def:
  with_zero f x y = if y = 0w then 0w else f x y
End

Definition b2w_def[simp]:
  b2w T = 1w ∧ b2w F = 0w
End

Definition step_inst_def:
    step_inst Stop = finish_context T [] 0 0
  ∧ step_inst Add = binop Add word_add
  ∧ step_inst Mul = binop Mul word_mul
  ∧ step_inst Sub = binop Sub word_sub
  ∧ step_inst Div = binop Div (with_zero word_div)
  ∧ step_inst SDiv = binop SDiv (with_zero word_quot)
  ∧ step_inst Mod = binop Mod (with_zero word_mod)
  ∧ step_inst SMod = binop SMod (with_zero word_rem)
  ∧ step_inst AddMod = (λs.
      ignore_bind (consume_gas (static_gas AddMod) s)
        (stack_op 3 (λl. with_zero word_mod
                           (word_add (EL 0 l) (EL 1 l))
                           (EL 2 l))))
  ∧ step_inst MulMod = (λs.
      ignore_bind (consume_gas (static_gas MulMod) s)
        (stack_op 3 (λl. with_zero word_mod
                           (word_mul (EL 0 l) (EL 1 l))
                           (EL 2 l))))
  ∧ step_inst Exp = (λs.
      ignore_bind (consume_gas (static_gas Exp) s)
        (λs. bind (get_current_context s)
          (λcontext s.
           if 2 ≤ LENGTH context.stack
           then
             let exponent = w2n (EL 1 context.stack) in
             let exponentByteSize = SUC (LOG2 exponent DIV 8) in
             let dynamicGas = 50 * exponentByteSize in
             let base = w2n (EL 0 context.stack) in
             let result = n2w (base ** exponent) in
             let newStack = result :: DROP 2 context.stack in
             ignore_bind (consume_gas dynamicGas s)
               (set_current_context (context with stack := newStack))
           else Done (Excepted StackUnderflow) s.accounts)))
  ∧ step_inst SignExtend = binop SignExtend (λn. word_sign_extend (w2n n))
  ∧ step_inst LT = binop LT (λx y. b2w (w2n x < w2n y))
  ∧ step_inst GT = binop GT (λx y. b2w (w2n x > w2n y))
  ∧ step_inst SLT = binop SLT (λx y. b2w $ word_lt x y)
  ∧ step_inst SGT = binop SGT (λx y. b2w $ word_gt x y)
  ∧ step_inst Eq = binop Eq (λx y. b2w (x = y))
  ∧ step_inst IsZero = monop IsZero (λx. b2w (x = 0w))
  ∧ step_inst And = binop And word_and
  ∧ step_inst Or = binop Or word_or
  ∧ step_inst XOr = binop XOr word_xor
  ∧ step_inst Not = monop Not word_1comp
  ∧ step_inst Byte = binop Byte ARB (* TODO: use get_byte *)
  ∧ step_inst ShL = binop ShL (λn w. word_lsl w (w2n n))
  ∧ step_inst ShR = binop ShR (λn w. word_lsr w (w2n n))
  ∧ step_inst SAR = binop SAR (λn w. word_asr w (w2n n))
  ∧ step_inst SHA3 = Step () (* TODO *)
  ∧ step_inst Address = (λs.
      ignore_bind (consume_gas (static_gas Address) s)
        (λs. bind (get_current_context s)
          (λcontext s.
            let newStack = w2w context.callParams.callee :: context.stack in
            if LENGTH newStack ≤ stack_limit
            then set_current_context (context with stack := newStack) s
            else Done (Excepted StackOverflow) s.accounts)))
  ∧ step_inst _ = Step () (* TODO *)
End

Definition step_def:
  step s =
  if s.contexts = [] then Done (Excepted Impossible) s.accounts else
  let ctx = HD s.contexts in
  let code = (s.accounts (ctx.callParams.callee)).code in
  if ctx.pc < LENGTH code then
  if IS_SOME (parse_opcode (DROP ctx.pc code)) then
    step_inst (THE (parse_opcode (DROP ctx.pc code))) s
  else Done (Excepted InvalidOpcode) s.accounts
  else Done (Excepted Impossible) s.accounts
End

val _ = export_theory();