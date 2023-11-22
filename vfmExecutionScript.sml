open HolKernel boolLib bossLib Parse
     monadsyntax byteTheory
     vfmTypesTheory vfmContextTheory;

val _ = new_theory"vfmExecution";

Datatype:
  exception =
  | OutOfGas
  | StackOverflow
  | StackUnderflow
  | InvalidJumpDest
  | StackDepthLimit
  | WriteInStaticContext
  | OutOfBoundsRead
  | InsufficientBalance
  | InvalidParameter
  | InvalidContractPrefix
  | AddressCollision
  | Impossible
End

Datatype:
  result =
  <| output   : byte list
   ; events   : event list
   ; refund   : num
   ; accounts : evm_accounts
   |>
End

Datatype:
  outcome =
  | Excepted exception
  | Reverted (byte list)
  | Finished result
End

Type transaction_result = “:(α + outcome) # transaction_state”;

Definition bind_def:
  bind g f s =
    case g s of
    | (INR e, s) => (INR e, s)
    | (INL x, s) => f x s
End

Definition return_def:
  return (x:α) s = (INL x, s) : α transaction_result
End

Definition ignore_bind_def:
  ignore_bind r f = bind r (λx. f)
End

Definition fail_def:
  fail e s = (INR (Excepted e), s)
End

Definition finish_def:
  finish r s = (INR (Finished r), s)
End

Definition assert_def:
  assert b e s = (if b then INL () else INR (Excepted e), s)
End

val _ = monadsyntax.declare_monad (
  "txn",
  { bind = “bind”, unit = “return”,
    ignorebind = SOME “ignore_bind”, choice = NONE,
    fail = SOME “fail”, guard = SOME “assert”
  }
);
val () = monadsyntax.enable_monad "txn";
val () = monadsyntax.enable_monadsyntax();

Definition keccak256_def:
  keccak256 (bytes : byte list) = ARB : bytes32 (* TODO *)
End

Definition write_memory_def:
  write_memory byteIndex bytes memory =
  let expandedMemory = PAD_RIGHT 0w (SUC byteIndex) memory in
  TAKE byteIndex expandedMemory ++ bytes
  ++ DROP (byteIndex + LENGTH bytes) expandedMemory
End

Definition get_current_context_def:
  get_current_context s =
  if s.contexts = [] then
    fail Impossible s
  else
    return (HD s.contexts) s
End

Definition get_tx_params_def:
  get_tx_params s = return s.txParams s
End

Definition get_accounts_def:
  get_accounts s = return s.accounts s
End

Definition update_accounts_def:
  update_accounts f s = return () (s with accounts updated_by f)
End

Definition set_accounts_def:
  set_accounts a = update_accounts (K a)
End

Definition set_accesses_def:
  set_accesses a s = return () (s with accesses := a)
End

Definition get_original_def:
  get_original s =
    if s.contexts = [] then
      fail Impossible s
    else
      return (LAST s.contexts).callParams.accounts s
End

Definition set_current_context_def:
  set_current_context c s =
  if s.contexts = [] then
    fail Impossible s
  else
    return () (s with contexts := c::(TL s.contexts))
End

Definition b2w_def[simp]:
  b2w T = 1w ∧ b2w F = 0w
End

Definition get_num_contexts_def:
  get_num_contexts s = return (LENGTH s.contexts) s
End

Definition push_context_def:
  push_context c = do
    value <<- c.callParams.value;
    caller <<- c.callParams.caller;
    callee <<- c.callParams.callee;
    accounts <- get_accounts;
    assert (value ≤ (accounts caller).balance) InsufficientBalance;
    newCaller <<- accounts caller with balance updated_by combin$C $- value;
    newCallee <<- accounts callee with balance updated_by $+ value;
    update_accounts $ (caller =+ newCaller) o (callee =+ newCallee);
    (λs. return () (s with contexts updated_by CONS c))
  od
End

Definition pop_context_def:
  pop_context s =
    return (HD s.contexts) (s with contexts := TL s.contexts)
End

Definition finish_context_def:
  finish_context success returnData = do
    n <- get_num_contexts;
    assert (0 < n) Impossible;
    if n = 1 then do
      context <- get_current_context;
      accounts <- get_accounts;
      finish <|
        output := returnData;
        events := context.logs;
        refund := context.gasRefund;
        accounts := accounts
      |>
    od else do
      callee <- pop_context;
      caller <- get_current_context;
      returnOffset <<- callee.callParams.retOffset;
      returnSize <<- callee.callParams.retSize;
      calleeGasLeft <<- callee.callParams.gasLimit - callee.gasUsed;
      newCallerBase <<- caller with
        <| returnData := returnData
         ; gasUsed    := caller.gasUsed - calleeGasLeft
         ; pc         := SUC caller.pc
         ; stack      := b2w success :: caller.stack
         ; memory     :=
             write_memory returnOffset (TAKE returnSize returnData) caller.memory
         |>;
      newCaller <<- if success
        then newCallerBase with
             <| gasRefund updated_by $+ callee.gasRefund
              ; logs updated_by combin$C APPEND callee.logs |>
        else newCallerBase;
      set_current_context newCaller;
      if success then return () else do
        set_accounts callee.callParams.accounts
      ; set_accesses callee.callParams.accesses
      od
    od
  od
End

Definition consume_gas_def:
  consume_gas n =
  do
    context <- get_current_context;
    newContext <<- context with gasUsed := context.gasUsed + n;
    assert (newContext.gasUsed ≤ context.callParams.gasLimit) OutOfGas;
    set_current_context newContext
  od
End

Definition refund_gas_def:
  refund_gas n = do
    context <- get_current_context;
    assert (n ≤ context.gasUsed) Impossible;
    newContext <<- context with gasUsed := context.gasUsed - n;
    set_current_context newContext
  od
End

Definition stack_op_def:
  stack_op n f =
  do
    context <- get_current_context;
    assert (n ≤ LENGTH context.stack) StackUnderflow;
    newStack <<- f (TAKE n context.stack) :: DROP n context.stack;
    set_current_context (context with stack := newStack)
  od
End

Definition monop_def:
  monop f = stack_op 1 (λl. f (EL 0 l))
End

Definition binop_def:
  binop f = stack_op 2 (λl. f (EL 0 l) (EL 1 l))
End

Definition push_from_tx_def:
  push_from_tx f =
  do
    context <- get_current_context;
    txParams <- get_tx_params;
    accounts <- get_accounts;
    newStack <<- f context txParams accounts :: context.stack;
    assert (LENGTH newStack ≤ stack_limit) StackOverflow;
    set_current_context (context with stack := newStack)
  od
End

Definition push_from_ctxt_def:
  push_from_ctxt f = push_from_tx (λctxt txParams accts. f ctxt)
End

Definition with_zero_def:
  with_zero f x y = if y = 0w then 0w else f x y
End

Definition word_size_def:
  word_size byteSize = (byteSize + 31) DIV 32
End

Definition memory_cost_def:
  memory_cost m =
  let byteSize = LENGTH m in
  let wordSize = word_size byteSize in
  (wordSize ** 32) DIV 512 + (3 * wordSize)
End

Definition memory_expansion_cost_def:
  memory_expansion_cost old new = memory_cost new - memory_cost old
End

Definition take_pad_0_def:
  take_pad_0 z l = PAD_RIGHT 0w z (TAKE z l)
End

Definition copy_to_memory_check_def:
  copy_to_memory_check checkSize f =
    bind get_current_context
      (λcontext.
        ignore_bind (assert (3 ≤ LENGTH context.stack) StackUnderflow) (
        let destOffset = w2n $ EL 0 context.stack in
        let offset = w2n $ EL 1 context.stack in
        let size = w2n $ EL 2 context.stack in
        let minimumWordSize = word_size size in
        bind get_accounts (λaccounts.
        let sourceBytes = f context accounts in
        ignore_bind
          (assert (¬checkSize ∨ offset + size ≤ LENGTH sourceBytes) OutOfBoundsRead) (
        let bytes = take_pad_0 size (DROP offset sourceBytes) in
        let expandedMemory = PAD_RIGHT 0w (minimumWordSize * 32) context.memory in
        let newMemory = write_memory destOffset bytes expandedMemory in
        let expansionCost = memory_expansion_cost context.memory newMemory in
        let dynamicGas = 3 * minimumWordSize + expansionCost in
        let newStack = DROP 3 context.stack in
        let newContext = context with
          <| stack := newStack; memory := newMemory |>
        in
          ignore_bind (consume_gas dynamicGas)
            (set_current_context newContext)))))
End

Definition copy_to_memory_def:
  copy_to_memory = copy_to_memory_check F
End

Definition store_to_memory_def:
  store_to_memory f =
    bind (get_current_context)
      (λcontext.
        ignore_bind (assert (2 ≤ LENGTH context.stack) StackUnderflow) (
          let byteIndex = w2n (EL 0 context.stack) in
          let value = EL 1 context.stack in
          let newMinSize = word_size (SUC byteIndex) * 32 in
          let expandedMemory = PAD_RIGHT 0w newMinSize context.memory in
          let newMemory = write_memory byteIndex (f value) expandedMemory in
          let expansionCost = memory_expansion_cost context.memory newMemory in
          let newStack = DROP 2 context.stack in
          let newContext =
            context with <| stack := newStack; memory := newMemory |>
          in
            ignore_bind (consume_gas expansionCost)
              (set_current_context newContext)))
End

Definition get_current_accesses_def:
  get_current_accesses s = return s.accesses s
End

Definition access_address_def:
  access_address a s =
  let addresses = s.accesses.addresses in
    return
      (a ∈ addresses)
      (s with accesses := (s.accesses with addresses := a INSERT addresses))
End

Definition access_slot_def:
  access_slot x s =
  let storageKeys = s.accesses.storageKeys in
    return
      (x ∈ storageKeys)
      (s with accesses := (s.accesses with storageKeys := x INSERT storageKeys))
End

Definition update_refund_def:
  update_refund f = do
    context <- get_current_context;
    newContext <<- context with gasRefund updated_by f;
    set_current_context newContext
  od
End

Definition assert_not_static_def:
  assert_not_static = do
    context <- get_current_context;
    assert (¬context.callParams.static) WriteInStaticContext
  od
End

(* TODO: move to separate theory *)
Definition rlp_bytes_def:
  rlp_bytes (bytes : byte list) =
  if LENGTH bytes = 1 ∧ w2n (HD bytes) < 128 then bytes
  else if LENGTH bytes < 56 then n2w (128 + LENGTH bytes) :: bytes
  else
    let lengthBytes = MAP n2w $ REVERSE $ n2l 256 $ LENGTH bytes
  in
    [n2w (183 + LENGTH lengthBytes)] ++ lengthBytes ++ bytes
End

Definition rlp_list_def:
  rlp_list (payload : byte list) =
  if LENGTH payload < 56 then n2w (192 + LENGTH payload) :: payload
  else
    let lengthBytes = MAP n2w $ REVERSE $ n2l 256 $ LENGTH payload
  in
    [n2w (248 + LENGTH lengthBytes)] ++ lengthBytes ++ payload
End

Definition step_inst_def:
    step_inst Stop = finish_context T []
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
  ∧ step_inst Exp =
      bind get_current_context
        (λcontext.
         ignore_bind (assert (2 ≤ LENGTH context.stack) StackUnderflow) (
           let exponent = w2n (EL 1 context.stack) in
           let exponentByteSize = SUC (LOG2 exponent DIV 8) in
           let dynamicGas = 50 * exponentByteSize in
           let base = w2n (EL 0 context.stack) in
           let result = n2w (base ** exponent) in
           let newStack = result :: DROP 2 context.stack in
           ignore_bind (consume_gas dynamicGas)
             (set_current_context (context with stack := newStack))))
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
  ∧ step_inst Byte = binop (λi w. w2w $ get_byte i w T)
  ∧ step_inst ShL = binop (λn w. word_lsl w (w2n n))
  ∧ step_inst ShR = binop (λn w. word_lsr w (w2n n))
  ∧ step_inst SAR = binop (λn w. word_asr w (w2n n))
  ∧ step_inst SHA3 = return () (* TODO *)
  ∧ step_inst Address = push_from_ctxt (λc. w2w c.callParams.callee)
  ∧ step_inst Balance = do
      context <- get_current_context;
      assert (1 ≤ LENGTH context.stack) StackUnderflow;
      address <<- w2w (EL 0 context.stack);
      warm <- access_address address;
      dynamicGas <<- if warm then 100 else 2600;
      accounts <- get_accounts;
      balance <<- (accounts address).balance;
      newStack <<- n2w balance :: TL context.stack;
      consume_gas dynamicGas;
      set_current_context (context with stack := newStack)
    od
  ∧ step_inst Origin = push_from_tx (λc t a. w2w t.origin)
  ∧ step_inst Caller = push_from_ctxt (λc. w2w c.callParams.caller)
  ∧ step_inst CallValue = push_from_ctxt (λc. n2w c.callParams.value)
  ∧ step_inst CallDataLoad =
      bind (get_current_context)
        (λcontext.
          ignore_bind (assert (1 ≤ LENGTH context.stack) StackUnderflow) (
            let index = w2n (EL 0 context.stack) in
            let bytes = take_pad_0 32 (DROP index context.callParams.data) in
            let newStack = word_of_bytes F 0w bytes :: TL context.stack in
            set_current_context (context with stack := newStack)))
  ∧ step_inst CallDataSize = push_from_ctxt (λc. n2w (LENGTH c.callParams.data))
  ∧ step_inst CallDataCopy =
      copy_to_memory (λcontext accounts. context.callParams.data)
  ∧ step_inst CodeSize = push_from_ctxt (λc. n2w (LENGTH c.callParams.code))
  ∧ step_inst CodeCopy =
      copy_to_memory (λcontext accounts. context.callParams.code)
  ∧ step_inst GasPrice = push_from_tx (λc t a. n2w t.gasPrice)
  ∧ step_inst ExtCodeSize =
      bind (get_current_context)
        (λcontext.
          ignore_bind (assert (1 ≤ LENGTH context.stack) StackUnderflow) (
            let address = w2w (EL 0 context.stack) in
            bind (access_address address) (λwarm.
            let dynamicGas = if warm then 100 else 2600 in
            bind get_accounts (λaccounts.
            let code = (accounts address).code in
            let newStack = n2w (LENGTH code) :: TL context.stack in
            let newContext = context with stack := newStack in
              ignore_bind
                (consume_gas dynamicGas)
                (set_current_context newContext)))))
  ∧ step_inst ExtCodeCopy =
      bind get_current_context
        (λcontext.
          ignore_bind (assert (1 ≤ LENGTH context.stack) StackUnderflow) (
            let address = w2w (EL 0 context.stack) in
            bind (access_address address) (λwarm.
            let addressAccessCost = if warm then 100 else 2600 in
            let newContext = context with stack := TL context.stack in
              ignore_bind
                (consume_gas addressAccessCost)
                (ignore_bind
                  (set_current_context newContext)
                  (copy_to_memory (λc accounts. (accounts address).code))))))
  ∧ step_inst ReturnDataSize = push_from_ctxt (λc. n2w (LENGTH c.returnData))
  ∧ step_inst ReturnDataCopy =
      copy_to_memory_check T (λcontext accounts. context.returnData)
  ∧ step_inst ExtCodeHash = return () (* TODO needs hash in state *)
  ∧ step_inst BlockHash = return () (* TODO needs hash in state *)
  ∧ step_inst CoinBase = push_from_tx (λc t a. w2w t.blockCoinBase)
  ∧ step_inst TimeStamp = push_from_tx (λc t a. n2w t.blockTimeStamp)
  ∧ step_inst Number = push_from_tx (λc t a. n2w t.blockNumber)
  ∧ step_inst PrevRandao = push_from_tx (λc t a. t.prevRandao)
  ∧ step_inst GasLimit = push_from_tx (λc t a. n2w t.blockGasLimit)
  ∧ step_inst ChainId = push_from_tx (λc t a. n2w t.chainId)
  ∧ step_inst SelfBalance =
      push_from_tx (λc t a. n2w (a c.callParams.callee).balance)
  ∧ step_inst BaseFee = push_from_tx (λc t a. n2w t.baseFee)
  ∧ step_inst Pop =
      bind get_current_context
        (λcontext.
          ignore_bind (assert (1 ≤ LENGTH context.stack) StackUnderflow) (
           set_current_context (context with stack := TL context.stack)))
  ∧ step_inst MLoad =
      bind get_current_context
        (λcontext.
          ignore_bind (assert (1 ≤ LENGTH context.stack) StackUnderflow) (
            let byteIndex = w2n (EL 0 context.stack) in
            let newMinSize = word_size (SUC byteIndex) * 32 in
            let newMemory = PAD_RIGHT 0w newMinSize context.memory in
            let expansionCost = memory_expansion_cost context.memory newMemory in
            let word = word_of_bytes F 0w (TAKE 32 (DROP byteIndex newMemory)) in
            let newStack = word :: TL context.stack in
            let newContext =
              context with <| stack := newStack; memory := newMemory |>
            in
              ignore_bind (consume_gas expansionCost)
                (set_current_context newContext)))
  ∧ step_inst MStore = store_to_memory (combin$C word_to_bytes F)
  ∧ step_inst MStore8 = store_to_memory (SINGL o w2w)
  ∧ step_inst SLoad =
      bind get_current_context
        (λcontext.
          ignore_bind (assert (1 ≤ LENGTH context.stack) StackUnderflow) (
            let key = EL 0 context.stack in
            let address = context.callParams.callee in
            bind (access_slot (address, key)) (λwarm.
            let dynamicGas = if warm then 100 else 2600 in
            bind get_accounts (λaccounts.
            let word = (accounts address).storage key in
            let newStack = word :: TL context.stack in
            let newContext = context with <| stack := newStack |> in
            ignore_bind (consume_gas dynamicGas)
              (set_current_context newContext)))))
  ∧ step_inst SStore = do
      context <- get_current_context;
      assert (2 ≤ LENGTH context.stack) StackUnderflow;
      gasLeft <<- context.callParams.gasLimit - context.gasUsed;
      assert (2300 < gasLeft) OutOfGas;
      key <<- EL 0 context.stack;
      value <<- EL 1 context.stack;
      address <<- context.callParams.callee;
      accounts <- get_accounts;
      account <<- accounts address;
      currentValue <<- account.storage key;
      original <- get_original;
      originalValue <<- (original address).storage key;
      slotWarm <- access_slot (address, key);
      baseDynamicGas <<-
        if originalValue = currentValue ∧ currentValue ≠ value
        then if originalValue = 0w then 20000 else 2900
        else 100;
      dynamicGas <<- baseDynamicGas + if slotWarm then 0 else 2100;
      refundUpdater <<-
        if currentValue ≠ value ∧ originalValue ≠ 0w then
          if currentValue = 0w then combin$C $- 15000
          else if value = 0w then $+ 15000 else I
        else I;
      newStorage <<- (key =+ value) account.storage;
      newAccount <<- account with storage := newStorage;
      newStack <<- DROP 2 context.stack;
      newContext <<- context with
        <| stack := newStack; gasRefund updated_by refundUpdater |>;
      consume_gas dynamicGas;
      assert (¬context.callParams.static) WriteInStaticContext;
      update_accounts (address =+ newAccount);
      set_current_context newContext
    od
  ∧ step_inst Jump =
      bind get_current_context
        (λcontext.
          ignore_bind (assert (1 ≤ LENGTH context.stack) StackUnderflow) (
            let dest = w2n $ EL 0 context.stack in
            let newContext =
              context with <| stack := TL context.stack; jumpDest := SOME dest |>
            in
              set_current_context newContext))
  ∧ step_inst JumpI =
      bind get_current_context
        (λcontext.
          ignore_bind (assert (2 ≤ LENGTH context.stack) StackUnderflow) (
            let dest = w2n $ EL 0 context.stack in
            let jumpDest = if EL 1 context.stack ≠ 0w then SOME dest else NONE in
            let newStack = DROP 2 context.stack in
            let newContext =
              context with <| stack := newStack; jumpDest := jumpDest |>
            in
              set_current_context newContext))
  ∧ step_inst PC = push_from_ctxt (λc. n2w c.pc)
  ∧ step_inst MSize = push_from_ctxt (λc. n2w $ LENGTH c.memory)
  ∧ step_inst Gas = push_from_ctxt (λc. n2w $ c.callParams.gasLimit - c.gasUsed)
  ∧ step_inst JumpDest = return ()
  ∧ step_inst (Push n ws) =
      bind get_current_context
        (λcontext.
          let word = word_of_bytes F 0w ws in
          let newStack = word :: context.stack in
          ignore_bind (assert (LENGTH newStack ≤ stack_limit) StackOverflow) (
          set_current_context (context with stack := newStack)))
  ∧ step_inst (Dup n) =
      bind (get_current_context)
        (λcontext.
          ignore_bind (assert (w2n n ≤ LENGTH context.stack) StackUnderflow) (
            let word = EL (w2n n) context.stack in
            let newStack = word :: context.stack in
            ignore_bind (assert (LENGTH newStack ≤ stack_limit) StackOverflow) (
            set_current_context (context with stack := newStack))))
  ∧ step_inst (Swap n) =
      bind get_current_context
        (λcontext.
          ignore_bind (assert (SUC (w2n n) ≤ LENGTH context.stack) StackUnderflow) (
            let top = HD context.stack in
            let swap = EL (w2n n) (TL context.stack) in
            let ignored = TAKE (w2n n) (TL context.stack) in
            let rest = DROP (w2n n) (TL context.stack) in
            let newStack = [swap] ++ ignored ++ [top] ++ rest in
              set_current_context (context with stack := newStack)))
  ∧ step_inst (Log n) = do
      context <- get_current_context;
      assert (¬context.callParams.static) WriteInStaticContext;
      assert (2 + w2n n ≤ LENGTH context.stack) StackUnderflow;
      offset <<- w2n $ EL 0 context.stack;
      size <<- w2n $ EL 1 context.stack;
      newMinSize <<- word_size (offset + size) * 32;
      newMemory <<- PAD_RIGHT 0w newMinSize context.memory;
      expansionCost <<- memory_expansion_cost context.memory newMemory;
      dynamicGas <<- 375 * w2n n + 8 * size + expansionCost;
      consume_gas dynamicGas;
      logger <<- context.callParams.callee;
      topics <<- TAKE (w2n n) (DROP 2 context.stack);
      data <<- TAKE size (DROP offset newMemory);
      event <<- <| logger := logger; topics := topics; data := data |>;
      newContext <<- context with logs := event :: context.logs;
      set_current_context newContext
    od
  ∧ step_inst Create = do
      context <- get_current_context;
      assert (3 ≤ LENGTH context.stack) StackUnderflow;
      value <<- w2n $ EL 0 context.stack;
      offset <<- w2n $ EL 1 context.stack;
      size <<- w2n $ EL 2 context.stack;
      sender <<- context.callParams.callee;
      accounts <- get_accounts;
      nonce <<- (accounts sender).nonce;
      rlpSender <<- rlp_bytes $ word_to_bytes sender T;
      rlpNonce <<- rlp_bytes $ MAP n2w $ REVERSE $ n2l 256 $ nonce;
      rlpBytes <<- rlp_list $ rlpSender ++ rlpNonce;
      hash <<- keccak256 $ rlpBytes;
      address <<- w2w hash;
      newStack <<- address :: DROP 3 context.stack;
      set_current_context (context with stack := newStack)
      (* TODO *)
    od
  ∧ step_inst Call = do
      context <- get_current_context;
      assert (7 ≤ LENGTH context.stack) StackUnderflow;
      gas <<- w2n $ EL 0 context.stack;
      address <<- w2w $ EL 1 context.stack;
      value <<- w2n $ EL 2 context.stack;
      argsOffset <<- w2n $ EL 3 context.stack;
      argsSize <<- w2n $ EL 4 context.stack;
      retOffset <<- w2n $ EL 5 context.stack;
      retSize <<- w2n $ EL 6 context.stack;
      newStack <<- DROP 7 context.stack;
      newMinSize <<- MAX
        (word_size (retOffset + retSize) * 32)
        (word_size (argsOffset + argsSize) * 32);
      newMemory <<- PAD_RIGHT 0w newMinSize context.memory;
      expansionCost <<- memory_expansion_cost context.memory newMemory;
      addressWarm <- access_address address;
      accessCost <<- if addressWarm then 100 else 2600;
      positiveValueCost <<- if 0 < value then 9000 else 0;
      accounts <- get_accounts;
      toAccount <<- accounts address;
      toAccountEmpty <<-
        toAccount.balance = 0 ∧ toAccount.nonce = 0 ∧ toAccount.code = [];
      transferCost <<- if 0 < value ∧ toAccountEmpty then 25000 else 0;
      consume_gas (expansionCost + accessCost + transferCost + positiveValueCost);
      gasLeft <<- context.callParams.gasLimit - context.gasUsed;
      stipend <<- if 0 < value then 2300 else 0;
      cappedGas <<- MIN gas (gasLeft - gasLeft DIV 64);
      assert (¬context.callParams.static) WriteInStaticContext;
      consume_gas cappedGas;
      accesses <- get_current_accesses;
      subContextTx <<- <|
          from     := context.callParams.callee
        ; to       := address
        ; value    := value
        ; gasLimit := cappedGas + stipend
        ; data     := TAKE argsSize (DROP argsOffset newMemory)
      |>;
      subContextParams <<- <|
        code      := toAccount.code
      ; accounts  := accounts
      ; accesses  := accesses
      ; retOffset := retOffset
      ; retSize   := retSize
      |>;
      subContext <<- initial_context subContextParams subContextTx;
      n <- get_num_contexts;
      assert (n < context_limit) StackDepthLimit;
      push_context subContext;
      n1 <- get_num_contexts;
      if n = n1
      then refund_gas subContextTx.gasLimit
      else return ()
    od
  ∧ step_inst CallCode = return () (* TODO *)
  ∧ step_inst Return = do
      context <- get_current_context;
      assert (2 ≤ LENGTH context.stack) StackUnderflow;
      offset <<- w2n $ EL 0 context.stack;
      size <<- w2n $ EL 1 context.stack;
      newMinSize <<- word_size (offset + size) * 32;
      expandedMemory <<- PAD_RIGHT 0w newMinSize context.memory;
      returnData <<- TAKE size (DROP offset expandedMemory);
      finish_context T returnData
    od
  ∧ step_inst DelegateCall = return () (* TODO *)
  ∧ step_inst Create2 = return () (* TODO *)
  ∧ step_inst StaticCall = return () (* TODO *)
  ∧ step_inst Revert = return () (* TODO *)
End

Definition inc_pc_def:
  inc_pc n =
  bind (get_current_context)
    (λcontext.
      case context.jumpDest of
      | NONE => set_current_context (context with pc := context.pc + n)
      | SOME pc =>
        let code = context.callParams.code in
        ignore_bind (assert
          (pc < LENGTH code ∧ parse_opcode (DROP pc code) = SOME JumpDest)
          InvalidJumpDest) (
        set_current_context (context with <| pc := pc; jumpDest := NONE |>)))
End

Definition step_def:
  step = do
    context <- get_current_context;
    code <<- context.callParams.code;
    if context.pc = LENGTH code
    then step_inst Stop
    else do
      assert (context.pc < LENGTH code) Impossible;
      case parse_opcode (DROP context.pc code) of
      | NONE => finish_context F []
      | SOME op => do
          consume_gas (static_gas op);
          step_inst op;
          inc_pc (LENGTH (opcode op))
        od
    od
  od
End

(* TODO: prove LENGTH memory is always a multiple of 32 bytes *)
(* TODO: define gas-oblivious execution semantics (where Gas is an invalid op) *)

val _ = export_theory();
