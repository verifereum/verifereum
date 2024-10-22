open HolKernel boolLib bossLib Parse
     monadsyntax byteTheory keccakTheory
     recursiveLengthPrefixTheory
     vfmTypesTheory vfmContextTheory;

val _ = new_theory "vfmExecution";

(* TODO: move? *)
Definition Keccak_256_bytes_def:
  Keccak_256_bytes (bs:word8 list) : word8 list =
    MAP bools_to_word $ chunks 8 $
    Keccak_256 $
    MAP ((=) 1) $ FLAT $
    MAP (PAD_RIGHT 0 8 o word_to_bin_list) bs
End

Datatype:
  exception =
  | OutOfGas
  | StackOverflow
  | StackUnderflow
  | InvalidJumpDest
  | WriteInStaticContext
  | OutOfBoundsRead
  | Reverted
  | Impossible
End

Type execution_result = “:(α + exception option) # execution_state”;

Definition bind_def:
  bind g f s : α execution_result =
    case g s of
    | (INR e, s) => (INR e, s)
    | (INL x, s) => f x s
End

Definition return_def:
  return (x:α) s = (INL x, s) : α execution_result
End

Definition ignore_bind_def:
  ignore_bind r f = bind r (λx. f)
End

Definition fail_def:
  fail e s = (INR (SOME e), s) : α execution_result
End

Definition finish_def:
  finish s = (INR NONE, s) : α execution_result
End

Definition revert_def:
  revert s = (INR (SOME Reverted), s) : α execution_result
End

Definition assert_def:
  assert b e s = (if b then INL () else INR (SOME e), s) : unit execution_result
End

val _ = monadsyntax.declare_monad (
  "evm_execution",
  { bind = “bind”, unit = “return”,
    ignorebind = SOME “ignore_bind”, choice = NONE,
    fail = SOME “fail”, guard = SOME “assert”
  }
);
val () = monadsyntax.enable_monad "evm_execution";
val () = monadsyntax.enable_monadsyntax();

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

Definition consume_gas_def:
  consume_gas n =
  do
    context <- get_current_context;
    newContext <<- context with gasUsed := context.gasUsed + n;
    assert (newContext.gasUsed ≤ context.callParams.gasLimit) OutOfGas;
    set_current_context newContext
  od
End

Definition unuse_gas_def:
  unuse_gas n = do
    context <- get_current_context;
    assert (n ≤ context.gasUsed) Impossible;
    newContext <<- context with gasUsed := context.gasUsed - n;
    set_current_context newContext
  od
End

Definition set_return_data_def:
  set_return_data rd = do
    context <- get_current_context;
    newContext <<- context with returnData := rd;
    set_current_context newContext
  od
End

Definition get_num_contexts_def:
  get_num_contexts s = return (LENGTH s.contexts) s
End

Definition push_context_def:
  push_context c = do
    n <- get_num_contexts;
    if n < context_limit
    then λs. return T $ s with contexts updated_by CONS c
    else do
      context <- get_current_context;
      set_current_context (context with stack := b2w F :: context.stack);
      return F
    od
  od
End

Definition code_for_transfer_def:
  code_for_transfer accounts (params: call_parameters) =
    case params.outputTo
    of Code address =>
      if (accounts address).code ≠ [] ∨
         (accounts address).nonce ≠ 0
      then opcode Invalid
      else params.code
    | _ => params.code
End

Definition context_for_transfer_def:
  context_for_transfer ctxt callerAddress incCaller code =
  ctxt with callParams updated_by
    (λp. p with <| accounts updated_by (callerAddress =+ incCaller)
                 ; code := code
                 ; parsed := parse_code 0 FEMPTY code
                 |>)
End

Definition start_context_def:
  start_context shouldTransfer c = do
    value <<- c.callParams.value;
    accounts <- get_accounts;
    callerAddress <<- c.callParams.caller;
    caller <<- accounts callerAddress;
    createAddress <<- case c.callParams.outputTo of Code a => SOME a | _ => NONE;
    shouldIncNonce <<- IS_SOME createAddress;
    if shouldTransfer then
      if value ≤ caller.balance ∧
         (shouldIncNonce ⇒ SUC caller.nonce < 2 ** 64)
      then do
        incCaller <<- caller with nonce updated_by SUC;
        code <<- code_for_transfer accounts c.callParams;
        ctxt <<- if shouldIncNonce
                 then context_for_transfer c callerAddress incCaller code
                 else c;
        success <- push_context ctxt;
        newCaller <<- (if success ∧ shouldIncNonce then incCaller else caller)
                      with balance updated_by flip $- value;
        (calleeAddress, newCallee) <<-
          case createAddress of
          | NONE => let a = c.callParams.callee in
                      (a, (accounts a) with balance updated_by $+ value)
          | SOME a => (a, (accounts a) with
                          <| nonce updated_by SUC; balance updated_by $+ value |>);
        update_accounts $
          (callerAddress =+ newCaller) o (calleeAddress =+ newCallee)
      od else do
        unuse_gas c.callParams.gasLimit;
        context <- get_current_context;
        set_current_context $ context with
          <| stack := b2w F :: context.stack
           ; returnData := []
           |>
      od
    else do push_context c; return () od
  od
End

Definition pop_stack_def:
  pop_stack n =
  do
    context <- get_current_context;
    stack <<- context.stack;
    assert (n ≤ LENGTH stack) StackUnderflow;
    return (TAKE n stack)
  od
End

Definition push_stack_def:
  push_stack v = do
    context <- get_current_context;
    stack <<- context.stack;
    assert (LENGTH stack < stack_limit) StackOverflow;
    set_current_context $
    context with stack := v :: context.stack
  od
End

Definition step_stop_def:
  step_stop = do set_return_data []; finish od
End

Definition step_binop_def:
  step_binop op f = do
    args <- pop_stack 2;
    consume_gas (static_gas op);
    push_stack $ f (EL 0 args) (EL 1 args);
  od
End

Definition step_modop_def:
  step_modop op f = do
    args <- pop_stack 3;
    consume_gas (static_gas op);
    a <<- w2n $ EL 0 args;
    b <<- w2n $ EL 1 args;
    n <<- w2n $ EL 2 args;
    push_stack $ if n = 0 then 0w else
      n2w $ (f a b) MOD n
  od
End

Definition with_zero_def:
  with_zero f x y = if y = 0w then 0w else f x y
End

Definition word_size_def:
  word_size byteSize = (byteSize + 31) DIV 32
End

Definition memory_cost_def:
  memory_cost byteSize =
  let wordSize = word_size byteSize in
  (wordSize * wordSize) DIV 512 + (3 * wordSize)
End

Definition memory_expansion_cost_def:
  memory_expansion_cost oldSize newMinSize =
  let newSize = MAX oldSize newMinSize in
    memory_cost newSize - memory_cost oldSize
End

Definition step_context_def:
  step_context op f = do
    consume_gas $ static_gas op;
    context <- get_current_context;
    push_stack $ f context
  od
End

Definition step_callParams_def:
  step_callParams op f = step_context op (λc. f c.callParams)
End

Definition step_txParams_def:
  step_txParams op f = do
    consume_gas $ static_gas op;
    txParams <- get_tx_params;
    push_stack $ f txParams
  od
End

Definition sign_extend_def:
  sign_extend (n:bytes32) (w:bytes32) : bytes32 =
  if n > 31w then w else
  let m = 31 - w2n n in
  let bs = DROP m $ word_to_bytes w T in
  let sign = if NULL bs then 0w else HD bs >> 7 in
  let sw = if sign = 0w then 0w else 255w in
    word_of_bytes T 0w $ REPLICATE m sw ++ bs
End

Definition step_exp_def:
  step_exp = do
    args <- pop_stack 2;
    base <<- EL 0 args;
    exponent <<- EL 1 args;
    exponentByteSize <<-
      if exponent = 0w then 0
      else SUC (LOG2 (w2n exponent) DIV 8);
    dynamicGas <<- 50 * exponentByteSize;
    consume_gas $ static_gas Exp + dynamicGas;
    result <<- word_exp base exponent;
    push_stack $ result
  od
End

Datatype:
  memory_expansion_info = <| cost: num; expand_by: num |>
End

Definition memory_expansion_info_def:
  memory_expansion_info offset size = do
    context <- get_current_context;
    oldSize <<- LENGTH context.memory;
    newMinSize <<- if 0 < size then word_size (offset + size) * 32 else 0;
    return $
      <| cost := memory_expansion_cost oldSize newMinSize
       ; expand_by := MAX oldSize newMinSize |>
  od
End

Definition expand_memory_def:
  expand_memory expand_by = do
    context <- get_current_context;
    set_current_context $
    context with memory := context.memory ++ REPLICATE expand_by 0w
  od
End

Definition read_memory_def:
  read_memory offset size = do
    context <- get_current_context;
    return $ TAKE size (DROP offset context.memory)
  od
End

Definition write_memory_def:
  write_memory byteIndex bytes = do
    context <- get_current_context;
    memory <<- context.memory;
    set_current_context $
      context with memory :=
        TAKE byteIndex memory ++ bytes
        ++ DROP (byteIndex + LENGTH bytes) memory
  od
End

Definition step_keccak256_def:
  step_keccak256 = do
    args <- pop_stack 2;
    offset <<- w2n (EL 0 args);
    size <<- w2n (EL 1 args);
    mx <- memory_expansion_info offset size;
    dynamicGas <<- 6 * word_size size + mx.cost;
    consume_gas $ static_gas Keccak256 + dynamicGas;
    expand_memory mx.expand_by;
    data <- read_memory offset size;
    hash <<- word_of_bytes T (0w:bytes32) $ Keccak_256_bytes $ REVERSE $ data;
    push_stack hash
  od
End

Definition push_from_tx_def:
  push_from_tx f =
  do
    context <- get_current_context;
    txParams <- get_tx_params;
    accounts <- get_accounts;
    push_stack $ f context txParams accounts
  od
End

Definition push_from_ctxt_def:
  push_from_ctxt f = push_from_tx (λctxt txParams accts. f ctxt)
End

Definition get_current_accesses_def:
  get_current_accesses s = return s.accesses s
End

Definition access_address_def:
  access_address a s =
  let addresses = s.accesses.addresses in
    return
      (if fIN a addresses then 100n else 2600)
      (s with accesses := (s.accesses with addresses := fINSERT a addresses))
End

Definition access_slot_def:
  access_slot x s =
  let storageKeys = s.accesses.storageKeys in
    return
      (if fIN x storageKeys then 100n else 2100)
      (s with accesses := (s.accesses with storageKeys := fINSERT x storageKeys))
End

Datatype:
  call_type = Normal | Code | Delegate | Static
End

Definition account_empty_def:
  account_empty a ⇔ a.balance = 0 ∧ a.nonce = 0 ∧ NULL a.code
End

Definition step_call_def:
  step_call call_type = do
    context <- get_current_context;
    stack <<- context.stack;
    valueOffset <<- if call_type = Delegate ∨ call_type = Static then 0 else 1;
    assert (6 + valueOffset ≤ LENGTH stack) StackUnderflow;
    gas <<- w2n $ EL 0 stack;
    address <<- w2w $ EL 1 stack;
    value <<- if valueOffset = 0 then 0 else w2n $ EL 2 stack;
    argsOffset <<- w2n $ EL (2 + valueOffset) stack;
    argsSize <<- w2n $ EL (3 + valueOffset) stack;
    retOffset <<- w2n $ EL (4 + valueOffset) stack;
    retSize <<- w2n $ EL (5 + valueOffset) stack;
    newStack <<- DROP (6 + valueOffset) stack;
    newMinSize <<- if retSize = 0 ∧ argsSize = 0 then 0 else
      MAX (word_size (retOffset + retSize) * 32)
          (word_size (argsOffset + argsSize) * 32);
    expansionCost <<- memory_expansion_cost context.memory newMinSize;
    addressWarm <- access_address address;
    accessCost <<- if addressWarm then 100 else 2600;
    positiveValueCost <<- if 0 < value then 9000 else 0;
    accounts <- get_accounts;
    toAccount <<- accounts address;
    toAccountEmpty <<- account_empty toAccount;
    transferCost <<- if call_type = Normal then
      if 0 < value ∧ toAccountEmpty then 25000 else 0
    else 0;
    consume_gas (expansionCost + accessCost + transferCost + positiveValueCost);
    assert (context.callParams.static ⇒ value = 0) WriteInStaticContext;
    newMemory <<- PAD_RIGHT 0w newMinSize context.memory;
    spentContext <- get_current_context;
    gasLeft <<- context.callParams.gasLimit - spentContext.gasUsed;
    stipend <<- if 0 < value then 2300 else 0;
    cappedGas <<- MIN gas (gasLeft - gasLeft DIV 64);
    consume_gas cappedGas;
    spentCappedContext <- get_current_context;
    accesses <- get_current_accesses;
    newContext <<- spentCappedContext with <| stack := newStack; memory := newMemory |>;
    set_current_context newContext;
    subContextTx <<- <|
        from     := if call_type = Delegate
                    then context.callParams.caller
                    else context.callParams.callee
      ; to       := if call_type = Code ∨ call_type = Delegate
                    then context.callParams.callee
                    else address
      ; value    := if call_type = Delegate
                    then context.callParams.value
                    else value
      ; gasLimit := cappedGas + stipend
      ; data     := TAKE argsSize (DROP argsOffset newMemory)
      (* unused: for concreteness *)
      ; nonce := 0; gasPrice := 0; accessList := []
    |>;
    subContextParams <<- <|
        code      := toAccount.code
      ; accounts  := accounts
      ; accesses  := accesses
      ; outputTo  := Memory <| offset := retOffset; size := retSize |>
      ; static    := if call_type = Static then T else context.callParams.static
    |>;
    subContext <<- initial_context subContextParams subContextTx;
    start_context (call_type = Normal ∨ call_type = Code) subContext
  od
End

Definition step_create_def:
  step_create two = do
    context <- get_current_context;
    stack <<- context.stack;
    saltOffset <<- if two then 1 else 0;
    assert (3 + saltOffset ≤ LENGTH stack) StackUnderflow;
    value <<- w2n $ EL 0 stack;
    offset <<- w2n $ EL 1 stack;
    size <<- w2n $ EL 2 stack;
    salt <<- if two then EL 3 stack else 0w;
    senderAddress <<- context.callParams.callee;
    accounts <- get_accounts;
    sender <<- accounts senderAddress;
    nonce <<- sender.nonce;
    rlpSender <<- rlp_bytes $ word_to_bytes senderAddress T;
    rlpNonce <<- rlp_bytes $ if nonce = 0 then [] else
                             MAP n2w $ REVERSE $ n2l 256 $ nonce;
    rlpBytes <<- rlp_list $ rlpSender ++ rlpNonce;
    hash <<- word_of_bytes T (0w:bytes32) $ Keccak_256_bytes $ rlpBytes;
    newMinSize <<- if 0 < size then word_size (offset + size) * 32 else 0;
    expansionCost <<- memory_expansion_cost context.memory newMinSize;
    newMemory <<- PAD_RIGHT 0w newMinSize context.memory;
    newStack <<- DROP (3 + saltOffset) stack;
    code <<- TAKE size (DROP offset newMemory);
    address <<-
      if two then w2w $ word_of_bytes T (0w:bytes32) $ Keccak_256_bytes(
        [n2w 0xff] ++
        word_to_bytes senderAddress T ++
        word_to_bytes salt T ++
        Keccak_256_bytes code)
      else w2w hash;
    access_address address;
    minimumWordSize <<- word_size size;
    readCodeCost <<- if two then 6 * minimumWordSize else 0;
    consume_gas (readCodeCost + expansionCost);
    spentContext0 <- get_current_context;
    gasLeft <<- spentContext0.callParams.gasLimit - spentContext0.gasUsed;
    cappedGas <<- gasLeft - gasLeft DIV 64;
    consume_gas cappedGas;
    assert (¬context.callParams.static) WriteInStaticContext;
    spentContext <- get_current_context;
    set_current_context $
      spentContext with <| stack := newStack; memory := newMemory |>;
    accesses <- get_current_accesses;
    subContextTx <<- <|
        from     := senderAddress
      ; to       := 0w
      ; value    := value
      ; gasLimit := cappedGas
      ; data     := []
      (* unused: for concreteness *)
      ; nonce := 0; gasPrice := 0; accessList := []
    |>;
    subContextParams <<- <|
        code      := code
      ; accounts  := accounts
      ; accesses  := accesses
      ; outputTo  := Code address
      ; static    := context.callParams.static
    |>;
    subContext <<- initial_context subContextParams subContextTx;
    start_context T subContext
  od
End

Definition step_sload_def:
  step_sload = do
    args <- pop_stack 1;
    key <<- EL 0 args;
    context <- get_current_context;
    address <<- context.callParams.callee;
    accessCost <- access_slot (SK address key);
    consume_gas $ static_gas SLoad + accessCost;
    accounts <- get_accounts;
    word <<- (accounts address).storage key;
    push_stack word
  od
End

Definition update_gas_refund_def:
  update_gas_refund (add, sub) = do
    context <- get_current_context;
    set_current_context $
      context with gasRefund updated_by (λx. x + add - sub)
  od
End

Definition assert_static_def:
  assert_static = do
    context <- get_current_context;
    assert (¬context.callParams.static) WriteInStaticContext
  od
End

Definition write_storage_def:
  write_storage address key value =
  update_accounts (λaccounts.
    let account = accounts address in
    let newAccount = account with storage updated_by (key =+ value);
    in (address =+ newAccount) accounts)
End

Definition step_sstore_def:
  step_sstore = do
    args <- pop_stack 2;
    key <<- EL 0 args;
    value <<- EL 1 args;
    context <- get_current_context;
    gasLeft <<- context.callParams.gasLimit - context.gasUsed;
    assert (2300 ≤ gasLeft) OutOfGas;
    address <<- context.callParams.callee;
    accounts <- get_accounts;
    currentValue <<- (accounts address).storage key;
    original <- get_original;
    originalValue <<- (original address).storage key;
    accessCost <- access_slot (SK address key);
    baseDynamicGas <<-
      if originalValue = currentValue ∧ currentValue ≠ value
      then if originalValue = 0w then 20000 else 2900
      else 100;
    dynamicGas <<- baseDynamicGas + if accessCost > 100 then accessCost else 0;
    refundUpdates <<-
      if currentValue ≠ value then
        let storageSetRefund =
          if originalValue = value then
            if originalValue = 0w then
              20000 - 100
            else
              5000 - 2100 - 100
          else 0
        in
          if originalValue ≠ 0w ∧ currentValue ≠ 0w ∧ value = 0w then
            (storageSetRefund + 15000, 0)
          else if originalValue ≠ 0w ∧ currentValue = 0w then
            (storageSetRefund, 15000)
          else (storageSetRefund, 0)
      else (0, 0);
    update_gas_refund refundUpdates;
    consume_gas dynamicGas;
    assert_static;
    write_storage address key value
  od
End

Definition transfer_value_def:
  transfer_value (fromAddress: address) toAddress value accounts =
  if value = 0 ∨ fromAddress = toAddress then accounts else
    let sender = accounts fromAddress in
    let recipient = accounts toAddress in
    let newSender = sender with balance updated_by flip $- value in
    let newRecipient = recipient with balance updated_by $+ value in
    (toAddress =+ newRecipient) $ (fromAddress =+ newSender) accounts
End

Definition step_balance_def:
  step_balance = do
    args <- pop_stack 1;
    address <<- w2w $ EL 0 args;
    accessCost <- access_address address;
    consume_gas $ static_gas Balance + accessCost;
    accounts <- get_accounts;
    balance <<- n2w $ (accounts address).balance;
    push_stack balance
  od
End

Definition step_call_data_load_def:
  step_call_data_load = do
    args <- pop_stack 1;
    index <<- w2n $ EL 0 args;
    consume_gas $ static_gas CallDataLoad;
    context <- get_current_context;
    bytes <<- take_pad_0 32 (DROP index context.callParams.data);
    push_stack $ word_of_bytes F 0w (REVERSE bytes)
  od
End

Definition copy_to_memory_def:
  copy_to_memory gas offset sourceOffset size getSource = do
    minimumWordSize <<- word_size size;
    mx <- memory_expansion_info offset size;
    dynamicGas <<- 3 * minimumWordSize + mx.cost;
    consume_gas $ gas + dynamicGas;
    sourceBytes <- getSource;
    bytes <<- take_pad_0 size (DROP sourceOffset sourceBytes);
    expand_memory mx.expand_by;
    write_memory offset bytes;
  od
End

Definition step_copy_to_memory_def:
  step_copy_to_memory op getSource = do
    args <- pop_stack 3;
    offset <<- w2n $ EL 0 args;
    sourceOffset <<- w2n $ EL 1 args;
    size <<- w2n $ EL 2 args;
    copy_to_memory (static_gas op) offset sourceOffset size getSource
  od
End

Definition get_return_data_def:
  get_return_data offset size = do
    context <- get_current_context;
    data <<- context.returnData;
    assert (offset + size ≤ LENGTH data) OutOfBoundsRead;
    return data
  od
End

Definition step_return_data_copy_def:
  step_return_data_copy = do
    args <- pop_stack 3;
    offset <<- w2n $ EL 0 args;
    sourceOffset <<- w2n $ EL 1 args;
    size <<- w2n $ EL 2 args;
    copy_to_memory (static_gas ReturnDataCopy)
    offset sourceOffset size (get_return_data sourceOffset size)
  od
End

Definition step_ext_code_size_def:
  step_ext_code_size = do
    args <- pop_stack 1;
    address <<- w2w $ EL 0 args;
    accessCost <- access_address address;
    consume_gas $ static_gas ExtCodeSize + accessCost;
    accounts <- get_accounts;
    code <<- (accounts address).code;
    push_stack $ n2w (LENGTH code)
  od
End

Definition get_code_def:
  get_code address = do
    accounts <- get_accounts;
    return $ (accounts address).code
  od
End

Definition get_current_code_def:
  get_current_code = do
    context <- get_current_context;
    return $ context.callParams.code
  od
End

Definition get_call_data_def:
  get_call_data = do
    context <- get_current_context;
    return $ context.callParams.data
  od
End

Definition step_ext_code_copy_def:
  step_ext_code_copy = do
    args <- pop_stack 4;
    address <<- w2w $ EL 0 args;
    offset <<- w2n $ EL 1 args;
    sourceOffset <<- w2n $ EL 2 args;
    size <<- w2n $ EL 3 args;
    accessCost <- access_address address;
    copy_to_memory (static_gas ExtCodeCopy + accessCost)
      offset sourceOffset size (get_code address)
  od
End

Definition step_ext_code_hash_def:
  step_ext_code_hash = do
    args <- pop_stack 1;
    address <<- w2w $ EL 0 args;
    accessCost <- access_address address;
    consume_gas $ static_gas ExtCodeHash + accessCost;
    accounts <- get_accounts;
    code <<- (accounts address).code;
    (* TODO: handle non-existent or destroyed accounts? (hash = 0) *)
    hash <<- if fIN address precompile_addresses then 0w
             else word_of_bytes T (0w:bytes32) $ Keccak_256_bytes $ code;
    push_stack hash
  od
End

Definition step_block_hash_def:
  step_block_hash = do
    args <- pop_stack 1;
    number <<- w2n $ EL 0 args;
    consume_gas $ static_gas BlockHash;
    tx <- get_tx_params;
    inRange <<- number < tx.blockNumber ∧ tx.blockNumber - 256 ≤ number;
    index <<- tx.blockNumber - number - 1;
    hash <<- if inRange ∧ index < LENGTH tx.prevHashes
             then EL index tx.prevHashes else 0w;
    push_stack hash
  od
End

Definition step_self_balance_def:
  step_self_balance = do
    consume_gas $ static_gas SelfBalance;
    accounts <- get_accounts;
    context <- get_current_context;
    address <<- context.callParams.callee;
    balance <<- n2w (accounts address).balance;
    push_stack balance
  od
End

Definition step_mload_def:
  step_mload = do
    args <- pop_stack 1;
    offset <<- w2n (EL 0 args);
    mx <- memory_expansion_info offset 32;
    consume_gas $ static_gas MLoad + mx.cost;
    expand_memory mx.expand_by;
    bytes <- read_memory offset 32;
    word <<- word_of_bytes F 0w $ REVERSE bytes;
    push_stack word
  od
End

Definition step_mstore_def:
  step_mstore op = do
    args <- pop_stack 2;
    offset <<- w2n $ EL 0 args;
    value <<- EL 1 args;
    size <<- if op = MStore8 then 1 else 32;
    bytes <<- if op = MStore8 then [w2w value] else word_to_bytes value F;
    mx <- memory_expansion_info offset size;
    consume_gas $ static_gas op + mx.cost;
    expand_memory mx.expand_by;
    write_memory offset bytes;
  od
End

Definition set_jump_dest_def:
  set_jump_dest jumpDest = do
    context <- get_current_context;
    set_current_context $
      context with jumpDest := jumpDest
  od
End

Definition step_jump_def:
  step_jump = do
    args <- pop_stack 1;
    dest <<- w2n $ EL 0 args;
    consume_gas $ static_gas Jump;
    set_jump_dest $ SOME dest;
  od
End

Definition step_jumpi_def:
  step_jumpi = do
    args <- pop_stack 2;
    dest <<- w2n $ EL 0 args;
    jumpDest <<- if EL 1 args = 0w then NONE else SOME dest;
    set_jump_dest jumpDest
  od
End

Definition step_push_def:
  step_push n ws = do
    consume_gas $ static_gas $ Push n ws;
    push_stack $ word_of_bytes F 0w $ REVERSE ws
  od
End

Definition step_dup_def:
  step_dup n = do
    consume_gas $ static_gas $ Dup n;
    context <- get_current_context;
    stack <<- context.stack;
    assert (n < LENGTH stack) StackUnderflow;
    word <<- EL n stack;
    push_stack word
  od
End

Definition step_swap_def:
  step_swap n = do
    consume_gas $ static_gas $ Swap n;
    context <- get_current_context;
    stack <<- context.stack;
    assert (SUC n < LENGTH stack) StackUnderflow;
    top <<- HD stack;
    swap <<- EL n (TL stack);
    ignored <<- TAKE n (TL stack);
    rest <<- DROP (SUC n) (TL stack);
    newStack <<- [swap] ++ ignored ++ [top] ++ rest;
    set_current_context $ context with stack := newStack
  od
End

Definition push_log_def:
  push_log e = do
    context <- get_current_context;
    set_current_context $ context with logs updated_by (CONS e)
  od
End

Definition step_log_def:
  step_log n = do
    args <- pop_stack $ 2 + n;
    offset <<- w2n $ EL 0 args;
    size <<- w2n $ EL 1 args;
    topics <<- DROP 2 args;
    mx <- memory_expansion_info offset size;
    dynamicGas <<- 375 * n + 8 * size + mx.cost;
    consume_gas $ (static_gas $ Log n) + dynamicGas;
    expand_memory mx.expand_by;
    assert_static;
    context <- get_current_context;
    address <<- context.callParams.callee;
    data <- read_memory offset size;
    event <<- <| logger := address; topics := topics; data := data |>;
    push_log event
  od
End

Definition step_return_def:
  step_return b = do
    args <- pop_stack 2;
    offset <<- w2n $ EL 0 args;
    size <<- w2n $ EL 1 args;
    mx <- memory_expansion_info offset size;
    consume_gas $ static_gas (if b then Return else Revert) + mx.cost;
    expand_memory mx.expand_by;
    returnData <- read_memory offset size;
    set_return_data returnData;
    if b then finish else revert
  od
End

Definition step_inst_def:
    step_inst Stop = do set_return_data []; finish od
  ∧ step_inst Add = step_binop Add word_add
  ∧ step_inst Mul = step_binop Mul word_mul
  ∧ step_inst Sub = step_binop Sub word_sub
  ∧ step_inst Div = step_binop Div $ with_zero word_div
  ∧ step_inst SDiv = step_binop SDiv $ with_zero word_quot
  ∧ step_inst Mod = step_binop Mod $ with_zero word_mod
  ∧ step_inst SMod = step_binop SMod $ with_zero word_rem
  ∧ step_inst AddMod = step_modop AddMod word_add
  ∧ step_inst MulMod = step_modop MulMod word_mul
  ∧ step_inst Exp = step_exp
  ∧ step_inst SignExtend = step_binop SignExtend sign_extend
  ∧ step_inst LT = step_binop LT (λx y. b2w (w2n x < w2n y))
  ∧ step_inst GT = step_binop GT (λx y. b2w (w2n x > w2n y))
  ∧ step_inst SLT = step_binop SLT (λx y. b2w $ word_lt x y)
  ∧ step_inst SGT = step_binop SGT (λx y. b2w $ word_gt x y)
  ∧ step_inst Eq = step_binop Eq (λx y. b2w (x = y))
  ∧ step_inst IsZero = step_monop IsZero (λx. b2w (x = 0w))
  ∧ step_inst And = step_binop And word_and
  ∧ step_inst Or = step_binop Or binop word_or
  ∧ step_inst XOr = step_binop XOr word_xor
  ∧ step_inst Not = step_monop Not word_1comp
  ∧ step_inst Byte = step_binop Byte (λi w. w2w $ get_byte i w T)
  ∧ step_inst ShL = step_binop ShL (λn w. word_lsl w (w2n n))
  ∧ step_inst ShR = step_binop ShR (λn w. word_lsr w (w2n n))
  ∧ step_inst SAR = step_binop SAR (λn w. word_asr w (w2n n))
  ∧ step_inst Keccak256 = step_keccak256
  ∧ step_inst Address = step_callParams Address (λc. w2w c.callee)
  ∧ step_inst Balance = step_balance
  ∧ step_inst Origin = step_txParams Origin (λt. w2w t.origin)
  ∧ step_inst Caller = step_callParams Caller (λc. w2w c.caller)
  ∧ step_inst CallValue = step_callParams CallValue (λc. n2w c.value)
  ∧ step_inst CallDataLoad = step_call_data_load
  ∧ step_inst CallDataSize = step_callParams CallDataSize (λc. n2w (LENGTH c.data))
  ∧ step_inst CallDataCopy = step_copy_to_memory CallDataCopy get_call_data
  ∧ step_inst CodeSize = step_callParams CodeSize (λc. n2w (LENGTH c.code))
  ∧ step_inst CodeCopy = step_copy_to_memory CodeCopy get_current_code
  ∧ step_inst GasPrice = step_txParams GasPrice (λt. n2w t.gasPrice)
  ∧ step_inst ExtCodeSize = step_ext_code_size
  ∧ step_inst ExtCodeCopy = step_ext_code_copy
  ∧ step_inst ReturnDataSize = step_context ReturnDataSize
                                 (λc. n2w $ LENGTH c.returnData)
  ∧ step_inst ReturnDataCopy = step_return_data_copy
  ∧ step_inst ExtCodeHash = step_ext_code_hash
  ∧ step_inst BlockHash = step_block_hash
  ∧ step_inst CoinBase = step_txParams CoinBase (λt. w2w t.blockCoinBase)
  ∧ step_inst TimeStamp = step_txParams TimeStamp (λt. n2w t.blockTimeStamp)
  ∧ step_inst Number = step_txParams Number (λt. n2w t.blockNumber)
  ∧ step_inst PrevRandao = step_txParams PrevRandao (λt. t.prevRandao)
  ∧ step_inst GasLimit = step_txParams GasLimit (λt. n2w t.blockGasLimit)
  ∧ step_inst ChainId = step_txParams ChainId (λt. n2w t.chainId)
  ∧ step_inst SelfBalance = step_self_balance
  ∧ step_inst BaseFee = step_txParams BaseFee (λt. n2w t.baseFeePerGas)
  ∧ step_inst Pop = do pop_stack 1; return () od
  ∧ step_inst MLoad = step_mload
  ∧ step_inst MStore = step_mstore MStore
  ∧ step_inst MStore8 = step_mstore MStore8
  ∧ step_inst SLoad = step_sload
  ∧ step_inst SStore = step_sstore
  ∧ step_inst Jump = step_jump
  ∧ step_inst JumpI = step_jumpi
  ∧ step_inst PC = step_context PC (λc. n2w c.pc)
  ∧ step_inst MSize = step_context MSize (λc. n2w $ LENGTH c.memory)
  ∧ step_inst Gas = step_context Gas
                      (λc. n2w $ c.callParams.gasLimit - c.gasUsed)
  ∧ step_inst JumpDest = consume_gas $ static_gas JumpDest
  ∧ step_inst (Push n ws) = step_push n ws
  ∧ step_inst (Dup n) = step_dup n
  ∧ step_inst (Swap n) = step_swap n
  ∧ step_inst (Log n) = step_log n
  ∧ step_inst Create = step_create F
  ∧ step_inst Call = step_call Normal
  ∧ step_inst CallCode = step_call Code
  ∧ step_inst Return = step_return T
  ∧ step_inst DelegateCall = step_call Delegate
  ∧ step_inst Create2 = step_create T
  ∧ step_inst StaticCall = step_call Static
  ∧ step_inst Revert = step_return F
  ∧ step_inst Invalid = do
      context <- get_current_context;
      consume_gas (context.callParams.gasLimit - context.gasUsed);
      set_return_data [];
      revert
    od
  ∧ step_inst SelfDestruct = do
      context <- get_current_context;
      stack <<- context.stack;
      assert (1 ≤ LENGTH stack) StackUnderflow;
      assert (¬context.callParams.static) WriteInStaticContext;
      address <<- w2w $ EL 0 stack;
      accounts <- get_accounts;
      sender <<- context.callParams.callee;
      balance <<- (accounts sender).balance;
      addressWarm <- access_address address;
      targetEmpty <<- account_empty $ accounts address;
      transferCost <<- if 0 < balance ∧ targetEmpty then 25000 else 0;
      accessCost <<- if addressWarm then 0 else 2600;
      dynamicGas <<- transferCost + accessCost;
      consume_gas dynamicGas;
      set_accounts $ transfer_value sender address balance accounts;
      (* TODO: destroy created contract if this is a contract creation *)
    od
End

Definition inc_pc_def:
  inc_pc n =
  bind (get_current_context)
    (λcontext.
      case context.jumpDest of
      | NONE => set_current_context (context with pc := context.pc + n)
      | SOME pc =>
        let code = context.callParams.code in
        let parsed = context.callParams.parsed in
        ignore_bind (assert
          (pc < LENGTH code ∧ FLOOKUP parsed pc = SOME JumpDest)
          InvalidJumpDest) (
        set_current_context (context with <| pc := pc; jumpDest := NONE |>)))
End

Definition pop_context_def:
  pop_context s =
    return (HD s.contexts) (s with contexts := TL s.contexts)
End

Definition is_call_def:
  is_call Call = T ∧
  is_call CallCode = T ∧
  is_call DelegateCall = T ∧
  is_call StaticCall = T ∧
  is_call Create = T ∧
  is_call Create2 = T ∧
  is_call _ = F
End

Definition step_def:
  step s = case do
    context <- get_current_context;
    code <<- context.callParams.code;
    parsed <<- context.callParams.parsed;
    if LENGTH code ≤ context.pc
    then step_inst Stop
    else do
      case FLOOKUP parsed context.pc of
      | NONE => step_inst Invalid
      | SOME op => do
          step_inst op;
          if is_call op then return ()
          else inc_pc (LENGTH (opcode op))
        od
    od
  od s of
  | (INL x, s) => (INL x, s)
  | (INR e, s) =>
      case s.contexts of
      | [] => (INR (SOME Impossible), s)
      | [_] => (INR e, s)
      | callee :: caller :: callStack =>
        let exceptionalHalt = (e ≠ NONE ∧ e ≠ SOME Reverted) in
        let calleeGasLeft =
          if exceptionalHalt then 0
          else callee.callParams.gasLimit - callee.gasUsed in
        let returnData =
          if exceptionalHalt then []
          else callee.returnData in
        let calleeSuccess = (e = NONE) in
        let (newCallerBase, success) =
          (case callee.callParams.outputTo of
           | Memory r =>
             (caller with
                <| returnData := returnData
                 ; stack      := b2w calleeSuccess :: caller.stack
                 ; pc         := SUC caller.pc
                 ; gasUsed    := caller.gasUsed - calleeGasLeft
                 ; memory     :=
                     write_memory r.offset (TAKE r.size returnData) caller.memory
                 |>, calleeSuccess)
           | Code address =>
             let codeGas = LENGTH returnData * 200 in
             let validCode = (case returnData of h::_ => h ≠ n2w 0xef | _ => T) in
             let callerGasLeft = caller.callParams.gasLimit - caller.gasUsed in
             let success = (calleeSuccess ∧ validCode ∧ codeGas ≤ callerGasLeft) in
             (caller with
                <| returnData := if success then [] else returnData
                 ; stack      := (if success then w2w address else b2w F)
                                 :: caller.stack
                 ; pc         := SUC caller.pc
                 ; gasUsed    := if success
                                 then caller.gasUsed + codeGas - calleeGasLeft
                                 else if calleeSuccess
                                 then caller.gasUsed - calleeGasLeft
                                 else caller.callParams.gasLimit
                 |>,
              success)) in
        let newCaller =
          if success
          then newCallerBase with
               <| gasRefund updated_by $+ callee.gasRefund
                ; logs updated_by flip APPEND callee.logs |>
          else newCallerBase in
        let stateWithContext = s with contexts := newCaller :: callStack in
        let updatedState =
          if success then
            case callee.callParams.outputTo of
            | Memory _ => stateWithContext
            | Code address => let accounts = stateWithContext.accounts in
              stateWithContext with accounts :=
                (address =+ accounts address with code := returnData) accounts
          else stateWithContext in
        (INL (),
         if success
         then updatedState
         else updatedState with <|
             accounts := callee.callParams.accounts
           ; accesses := callee.callParams.accesses
           |>)
End

Definition run_def:
  run s = OWHILE (ISL o FST) (step o SND) (INL (), s)
End

Definition empty_return_destination_def:
  empty_return_destination = Memory <| offset := 0; size := 0 |>
End

Datatype:
  transaction_result =
  <| gasUsed  : num
   ; logs     : event list
   ; output   : byte list
   ; result   : exception option
   |>
End

Definition post_transaction_accounting_def:
  post_transaction_accounting blk tx result acc t =
  let exceptionalHalt = (result ≠ NONE ∧ result ≠ SOME Reverted) in
  let (gasLimit, gasUsed, refund, logs, returnData) =
    if NULL t.contexts ∨ ¬NULL (TL t.contexts)
    then (0, 0, 0, [], MAP (n2w o ORD) "not exactly one remaining context")
    else let ctxt = HD t.contexts in
      (ctxt.callParams.gasLimit, ctxt.gasUsed,
       ctxt.gasRefund, ctxt.logs,
       if exceptionalHalt then [] else ctxt.returnData) in
  let gasLeft = if exceptionalHalt then 0 else gasLimit - gasUsed in
  let txGasUsed = tx.gasLimit - gasLeft in
  let gasRefund = if result ≠ NONE then 0
                  else MIN (txGasUsed DIV 5) refund in
  let refundEther = (gasLeft + gasRefund) * tx.gasPrice in
  let priorityFeePerGas = tx.gasPrice - blk.baseFeePerGas in
  let totalGasUsed = txGasUsed - gasRefund in
  let transactionFee = totalGasUsed * priorityFeePerGas in
  let accounts = if result = NONE then t.accounts else acc in
  let sender = accounts tx.from in
  let feeRecipient = accounts blk.coinBase in
  let newAccounts =
    (tx.from =+ sender with balance updated_by $+ refundEther) $
    (blk.coinBase =+ feeRecipient with balance updated_by $+ transactionFee)
    accounts in
  let logs = if result = NONE then logs else [] in
  let tr = <| gasUsed := totalGasUsed;
              logs := logs;
              result := result;
              output := returnData |> in
  (tr, newAccounts)
End

Definition run_transaction_def:
  run_transaction chainId prevHashes blk accounts tx =
  OPTION_BIND
    (initial_state chainId prevHashes blk accounts empty_return_destination tx)
    (λs.
        case run (s with accounts updated_by
                  transfer_value tx.from tx.to tx.value) of
        | SOME (INR r, t) => SOME $
            post_transaction_accounting blk tx r s.accounts t
        | _ => NONE)
End

Definition update_beacon_block_def:
  update_beacon_block b (accounts: evm_accounts) =
  let addr = 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02w in
  let buffer_length = 8191n in
  let timestamp_idx = b.timeStamp MOD buffer_length in
  let root_idx = timestamp_idx + buffer_length in
  let a = accounts addr in
  let s0 = a.storage in
  let s1 = (n2w timestamp_idx =+ n2w b.timeStamp) s0 in
  let s2 = (n2w root_idx =+ b.parentBeaconBlockRoot) s1 in
  (addr =+ a with storage := s2) accounts
End

Definition run_block_def:
  run_block chainId prevHashes accounts b =
  FOLDL
    (λx tx.
       OPTION_BIND x (λ(ls, a).
         OPTION_MAP (λ(r, a). (SNOC r ls, a)) $
         run_transaction chainId prevHashes b a tx))
    (SOME ([], update_beacon_block b accounts))
    b.transactions
End

val _ = export_theory();
