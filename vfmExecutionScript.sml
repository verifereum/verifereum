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
  set_byte i b w =
      word_slice 256 ((SUC i) * 8) w ||
      w2w b << i ||
      word_slice (i * 8) 0 w
End

Definition word_of_bytes_def:
  (word_of_bytes be a [] = 0w) /\
  (word_of_bytes be a (b::bs) =
     set_byte a b (word_of_bytes be (SUC a) bs))
End

Definition write_memory_def:
    write_memory byteIndex [] memory = memory
  ∧ write_memory byteIndex (byte::bytes) memory =
      let wordIndex = byteIndex DIV 32 in
      let word = case FLOOKUP memory wordIndex of SOME w => w | NONE => 0w in
      let newWord = set_byte (byteIndex MOD 32) byte word in
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

Definition b2w_def[simp]:
  b2w T = 1w ∧ b2w F = 0w
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
       ; stack      := b2w success :: caller.stack
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
  monop f = stack_op 1 (λl. f (EL 0 l))
End

Definition binop_def:
  binop f = stack_op 2 (λl. f (EL 0 l) (EL 1 l))
End

Definition get_from_tx_def:
  get_from_tx f s =
    bind (get_current_context s)
      (λcontext s.
        let newStack = f context s.txParams s.accounts :: context.stack in
        if LENGTH newStack ≤ stack_limit
        then set_current_context (context with stack := newStack) s
        else Done (Excepted StackOverflow) s.accounts)
End

Definition get_from_ctxt_def:
  get_from_ctxt f = get_from_tx (λctxt txParams accts. f ctxt)
End

Definition with_zero_def:
  with_zero f x y = if y = 0w then 0w else f x y
End

Definition memory_cost_def:
  memory_cost m =
  let byteSize = CARD (FDOM m) in
  let wordSize = (byteSize + 31) DIV 32 in
  (wordSize ** 32) DIV 512 + (3 * wordSize)
End

Definition memory_expansion_cost_def:
  memory_expansion_cost old new = memory_cost new - memory_cost old
End

Definition take_pad_0_def:
  take_pad_0 z l = PAD_RIGHT 0w z (TAKE z l)
End

Definition copy_to_memory_def:
  copy_to_memory f s =
    bind (get_current_context s)
      (λcontext s.
        if 3 ≤ LENGTH context.stack then
        let destOffset = w2n $ EL 0 context.stack in
        let offset = w2n $ EL 1 context.stack in
        let size = w2n $ EL 2 context.stack in
        let minimumWordSize = (size + 31) DIV 32 in
        let bytes = take_pad_0 size (DROP offset (f context s)) in
        let newMemory = write_memory destOffset bytes context.memory in
        let expansionCost = memory_expansion_cost context.memory newMemory in
        let dynamicGas = 3 * minimumWordSize + expansionCost in
        let newStack = DROP 3 context.stack in
        let newContext = context with
          <| stack := newStack; memory := newMemory |>
        in
          ignore_bind (consume_gas dynamicGas s)
            (set_current_context newContext)
        else Done (Excepted StackUnderflow) s.accounts)
End

Definition step_inst_def:
    step_inst Stop = finish_context T [] 0 0
  ∧ step_inst Add = binop word_add
  ∧ step_inst Mul = binop word_mul
  ∧ step_inst Sub = binop word_sub
  ∧ step_inst Div = binop $ with_zero word_div
  ∧ step_inst SDiv = binop $ with_zero word_quot
  ∧ step_inst Mod = binop $ with_zero word_mod
  ∧ step_inst SMod = binop $ with_zero word_rem
  ∧ step_inst AddMod = stack_op 3
      (λl. with_zero word_mod
             (word_add (EL 0 l) (EL 1 l))
             (EL 2 l))
  ∧ step_inst MulMod = stack_op 3
      (λl. with_zero word_mod
             (word_mul (EL 0 l) (EL 1 l))
             (EL 2 l))
  ∧ step_inst Exp = (λs.
      bind (get_current_context s)
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
         else Done (Excepted StackUnderflow) s.accounts))
  ∧ step_inst SignExtend = binop (λn. word_sign_extend (w2n n))
  ∧ step_inst LT = binop (λx y. b2w (w2n x < w2n y))
  ∧ step_inst GT = binop (λx y. b2w (w2n x > w2n y))
  ∧ step_inst SLT = binop (λx y. b2w $ word_lt x y)
  ∧ step_inst SGT = binop (λx y. b2w $ word_gt x y)
  ∧ step_inst Eq = binop (λx y. b2w (x = y))
  ∧ step_inst IsZero = monop (λx. b2w (x = 0w))
  ∧ step_inst And = binop word_and
  ∧ step_inst Or = binop word_or
  ∧ step_inst XOr = binop word_xor
  ∧ step_inst Not = monop word_1comp
  ∧ step_inst Byte = binop ARB (* TODO: use get_byte *)
  ∧ step_inst ShL = binop (λn w. word_lsl w (w2n n))
  ∧ step_inst ShR = binop (λn w. word_lsr w (w2n n))
  ∧ step_inst SAR = binop (λn w. word_asr w (w2n n))
  ∧ step_inst SHA3 = Step () (* TODO *)
  ∧ step_inst Address = get_from_ctxt (λc. w2w c.callParams.callee)
  ∧ step_inst Balance = (λs.
      bind (get_current_context s)
        (λcontext s.
          if 1 ≤ LENGTH context.stack then
          let address = w2w (EL 0 context.stack) in
          let dynamicGas = if address ∈ s.accesses.addresses
                           then 100 else 2600 in
          (* TODO: add address to access set (and for other instructions too) *)
          let balance = (s.accounts address).balance in
          let newStack = n2w balance :: TL context.stack in
            ignore_bind (consume_gas dynamicGas s)
              (set_current_context (context with stack := newStack))
          else Done (Excepted StackUnderflow) s.accounts))
  ∧ step_inst Origin = get_from_tx (λc t a. w2w t.origin)
  ∧ step_inst Caller = get_from_ctxt (λc. w2w c.callParams.caller)
  ∧ step_inst CallValue = get_from_ctxt (λc. n2w c.callParams.value)
  ∧ step_inst CallDataLoad = (λs.
      bind (get_current_context s)
        (λcontext s.
          if 1 ≤ LENGTH context.stack
          then
            let index = w2n (EL 0 context.stack) in
            let bytes = take_pad_0 32 (DROP index context.callParams.data) in
            let newStack = word_of_bytes F 0 bytes :: TL context.stack in
            set_current_context (context with stack := newStack) s
          else Done (Excepted StackUnderflow) s.accounts))
  ∧ step_inst CallDataSize = get_from_ctxt (λc. n2w (LENGTH c.callParams.data))
  ∧ step_inst CallDataCopy =
      copy_to_memory (λcontext s. context.callParams.data)
  ∧ step_inst CodeSize =
      get_from_tx (λc t a. n2w (LENGTH (a c.callParams.codeAcct).code))
  ∧ step_inst CodeCopy =
      copy_to_memory (λcontext s. (s.accounts context.callParams.codeAcct).code)
  ∧ step_inst GasPrice = get_from_tx (λc t a. n2w t.gasPrice)
  ∧ step_inst ExtCodeSize = Step () (* TODO *)
  ∧ step_inst ExtCodeCopy = Step () (* TODO *)
  ∧ step_inst ReturnDataSize = get_from_ctxt (λc. n2w (LENGTH c.returnData))
  ∧ step_inst ReturnDataCopy = Step () (* TODO *)
  ∧ step_inst ExtCodeHash = Step () (* TODO *)
  (* TODO: needs the hashes to be in the state
  ∧ step_inst BlockHash = (λs.
      ignore_bind (consume_gas (static_gas BlockHash) s)
      (λs.
  *)
  ∧ step_inst CoinBase = get_from_tx (λc t a. w2w t.blockCoinBase)
  ∧ step_inst TimeStamp = get_from_tx (λc t a. n2w t.blockTimeStamp)
  ∧ step_inst Number = get_from_tx (λc t a. n2w t.blockNumber)
  ∧ step_inst PrevRandao = get_from_tx (λc t a. t.prevRandao)
  ∧ step_inst GasLimit = get_from_tx (λc t a. n2w t.blockGasLimit)
  ∧ step_inst ChainId = get_from_tx (λc t a. n2w t.chainId)
  ∧ step_inst SelfBalance =
      get_from_tx (λc t a. n2w (a c.callParams.callee).balance)
  ∧ step_inst BaseFee = get_from_tx (λc t a. n2w t.baseFee)
  ∧ step_inst Pop = (λs.
      bind (get_current_context s)
        (λcontext s.
         if context.stack ≠ []
         then
           set_current_context (context with stack := TL context.stack) s
         else Done (Excepted StackUnderflow) s.accounts))
  ∧ step_inst MLoad = Step () (* TODO *)
  ∧ step_inst _ = Step () (* TODO *)
End

Definition step_def:
  step s =
  bind (get_current_context s)
  (λcontext s.
    let code = (s.accounts (context.callParams.codeAcct)).code in
    if context.pc < LENGTH code then
    if IS_SOME (parse_opcode (DROP context.pc code)) then
      let op = (THE (parse_opcode (DROP context.pc code))) in
        ignore_bind (consume_gas (static_gas op) s) $ step_inst op
    else Done (Excepted InvalidOpcode) s.accounts
    else Done (Excepted Impossible) s.accounts)
End

val _ = export_theory();
