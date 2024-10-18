open HolKernel boolLib bossLib Parse
     monadsyntax byteTheory keccakTheory
     recursiveLengthPrefixTheory
     vfmTypesTheory vfmContextTheory;

val _ = new_theory "vfmExecution";

(* TODO: move? *)
Definition Keccak_256_bytes_def:
  Keccak_256_bytes (bs:word8 list) : word8 list =
    MAP bools_to_word $
    chunks 8 $
    Keccak_256 $
    MAP ((=) 1) $ FLAT $
    MAP (PAD_LEFT 0 8 o word_to_bin_list) bs
End

(* TODO: move *)

open arithmeticTheory wordsTheory wordsLib dividesTheory dep_rewrite

Definition word_exp_def:
  word_exp (b: 'a word) (e: 'a word) =
  if e = 0w then 1w else
  if word_mod e 2w = 0w then
    let x = word_exp b (word_div e 2w) in
      word_mul x x
  else word_mul b (word_exp b (e - 1w))
Termination
  WF_REL_TAC`measure (w2n o SND)`
  \\ Cases_on`dimword(:'a) = 2`
  >- ( `2w = 0w` by simp[] \\ pop_assum SUBST1_TAC \\ gs[word_mod_def] )
  \\ `2 < dimword(:'a)`
  by ( CCONTR_TAC
    \\ gs[NOT_LESS, NUMERAL_LESS_THM,
          LESS_OR_EQ, ONE_LT_dimword, ZERO_LT_dimword] )
  \\ qx_gen_tac`e` \\ rw[]
  \\ qspec_then`2w` mp_tac WORD_DIVISION
  \\ impl_tac >- rw[n2w_11]
  \\ disch_then(qspec_then`e`mp_tac)
  \\ rewrite_tac[word_div_def, word_mul_n2w, word_lo_n2w, GSYM WORD_LO]
  \\ `w2n e < dimword (:'a)` by simp[w2n_lt]
  \\ `w2n e DIV 2 < dimword(:'a)` by simp[DIV_LT_X]
  \\ Cases_on`e`
  \\ gs[word_lo_n2w]
End

Theorem MOD_MOD_LESS:
  0 < y /\ y < z ==> x MOD y MOD z = x MOD y
Proof
  strip_tac
  \\ irule LESS_MOD
  \\ irule LESS_TRANS
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ irule MOD_LESS
  \\ simp[]
QED

Theorem word_exp_EXP:
  ∀b e. word_exp b e = n2w $ w2n b ** w2n e
Proof
  recInduct word_exp_ind
  \\ rw[]
  \\ simp[Once word_exp_def]
  \\ IF_CASES_TAC >- gs[]
  \\ Cases_on`dimword(:'a) = 2`
  >- (
    gs[word_mod_def, word_div_def]
    \\ `w2n b < 2 ∧ w2n e < 2` by metis_tac[w2n_lt]
    \\ gs[NUMERAL_LESS_THM]
    \\ Cases_on`b` \\ gs[] )
  \\ `2 < dimword(:'a)`
  by (
    CCONTR_TAC
    \\ gs[NOT_LESS, LESS_OR_EQ, NUMERAL_LESS_THM,
          ONE_LT_dimword, ZERO_LT_dimword] )
  \\ `w2n e < dimword (:'a)` by simp[w2n_lt]
  \\ `w2n e DIV 2 < dimword(:'a)` by simp[DIV_LT_X]
  \\ Cases_on`e` \\ gs[word_mod_def, word_div_def]
  \\ Cases_on`b` \\ gs[]
  \\ gs[GSYM EXP_EXP_MULT]
  \\ DEP_REWRITE_TAC[MOD_MOD_LESS]
  \\ gs[]
  \\ IF_CASES_TAC \\ gs[]
  >- (
    AP_THM_TAC \\ AP_TERM_TAC
    \\ DEP_REWRITE_TAC[DIVIDES_DIV, DIVIDES_MOD_0]
    \\ simp[] )
  \\ simp[word_mul_n2w]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rewrite_tac[GSYM word_sub_def]
  \\ DEP_REWRITE_TAC[GSYM n2w_sub]
  \\ Cases_on`n` \\ gs[EXP]
QED

Definition word_exp_aux_def:
  word_exp_aux (b:'a word) (e:'a word) a =
  if e = 0w then a else
  if word_mod e 2w = 0w then
    word_exp_aux (word_mul b b) (word_div e 2w) a
  else
    word_exp_aux b (word_sub e 1w) (word_mul b a)
Termination
  WF_REL_TAC`measure (w2n o FST o SND)`
  \\ Cases_on`dimword(:'a) = 2`
  >- ( `2w = 0w` by simp[] \\ pop_assum SUBST1_TAC \\ gs[word_mod_def] )
  \\ `2 < dimword(:'a)`
  by ( CCONTR_TAC
    \\ gs[NOT_LESS, NUMERAL_LESS_THM,
          LESS_OR_EQ, ONE_LT_dimword, ZERO_LT_dimword] )
  \\ qx_gen_tac`e` \\ rw[]
  \\ Cases_on`e`
  \\ gs[word_div_def, word_mod_def, MOD_MOD_LESS]
  \\ DEP_REWRITE_TAC[LESS_MOD]
  \\ conj_asm2_tac \\ gs[DIV_LT_X]
End

Theorem word_exp_aux_EXP:
  !b e a. word_exp_aux b e a = n2w $ w2n a * w2n b ** w2n e
Proof
  recInduct word_exp_aux_ind
  \\ rpt strip_tac
  \\ simp[Once word_exp_aux_def]
  \\ IF_CASES_TAC \\ gs[]
  \\ Cases_on`dimword(:'a) = 2`
  >- (
    `2w = 0w` by simp[] \\ pop_assum SUBST1_TAC
    \\ gs[word_mod_def]
    \\ rewrite_tac[GSYM word_sub_def]
    \\ Cases_on`e`
    \\ DEP_REWRITE_TAC[GSYM n2w_sub]
    \\ conj_asm1_tac \\ gs[]
    \\ Cases_on`n` \\ gs[EXP]
    \\ Cases_on`a` \\ Cases_on`b`
    \\ gs[word_mul_n2w])
  \\ `2 < dimword(:'a)`
  by ( CCONTR_TAC
    \\ gs[NOT_LESS, NUMERAL_LESS_THM,
          LESS_OR_EQ, ONE_LT_dimword, ZERO_LT_dimword] )
  \\ Cases_on`e` \\ gs[word_mod_def, word_div_def]
  \\ reverse IF_CASES_TAC \\ gs[MOD_MOD_LESS]
  >- (
    rewrite_tac[GSYM word_sub_def]
    \\ `1 ≤ n` by simp[]
    \\ asm_simp_tac std_ss [GSYM n2w_sub, w2n_n2w]
    \\ `(n - 1) MOD dimword(:'a) = n - 1`
    by ( DEP_REWRITE_TAC[LESS_MOD] \\ simp[] )
    \\ pop_assum SUBST_ALL_TAC
    \\ Cases_on`a` \\ Cases_on`b`
    \\ gs[word_mul_n2w]
    \\ Cases_on`n` \\ gs[EXP] )
  \\ `(n DIV 2) MOD dimword(:'a) = n DIV 2`
  by ( DEP_REWRITE_TAC[LESS_MOD] \\ gs[DIV_LT_X] )
  \\ pop_assum SUBST_ALL_TAC
  \\ Cases_on`a` \\ Cases_on`b`
  \\ gs[word_mul_n2w]
  \\ gs[GSYM EXP_EXP_MULT]
  \\ DEP_REWRITE_TAC[DIVIDES_DIV]
  \\ gs[DIVIDES_MOD_0]
QED

Theorem word_exp_aux:
  word_exp b e = word_exp_aux b e 1w
Proof
  rw[word_exp_EXP, word_exp_aux_EXP]
QED

(* -- *)

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
  | MissingHashes
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
      then [invalid_opcode]
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
  start_context shouldTransfer shouldIncNonce c = do
    value <<- c.callParams.value;
    callerAddress <<- c.callParams.caller;
    accounts <- get_accounts;
    caller <<- accounts callerAddress;
    if shouldTransfer then
      if value ≤ caller.balance ∧
         (shouldIncNonce ⇒ SUC caller.nonce < 2 ** 64)
      then do
        calleeAddress <<- c.callParams.callee;
        incCaller <<- caller with nonce updated_by SUC;
        code <<- code_for_transfer accounts c.callParams;
        ctxt <<- if shouldIncNonce
                 then context_for_transfer c callerAddress incCaller code
                 else c;
        success <- push_context ctxt;
        newCaller <<- (if success ∧ shouldIncNonce then incCaller else caller)
                      with balance updated_by flip $- value;
        newCallee <<- accounts calleeAddress with balance updated_by $+ value;
        update_accounts $ (callerAddress =+ newCaller) o (calleeAddress =+ newCallee)
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

Definition modop_def:
  modop f (l: bytes32 list) : bytes32 =
  let a = w2n $ EL 0 l in
  let b = w2n $ EL 1 l in
  let n = w2n $ EL 2 l in
    if n = 0 then 0w
    else n2w $ (f a b) MOD n
End

Definition word_size_def:
  word_size byteSize = (byteSize + 31) DIV 32
End

Definition memory_cost_def:
  memory_cost m =
  let byteSize = LENGTH m in
  let wordSize = word_size byteSize in
  (wordSize * wordSize) DIV 512 + (3 * wordSize)
End

Definition memory_expansion_cost_def:
  memory_expansion_cost old new = memory_cost new - memory_cost old
End

Definition copy_to_memory_check_def:
  copy_to_memory_check checkSize f = do
    context <- get_current_context;
    assert (3 ≤ LENGTH context.stack) StackUnderflow;
    destOffset <<- w2n $ EL 0 context.stack;
    offset <<- w2n $ EL 1 context.stack;
    size <<- w2n $ EL 2 context.stack;
    minimumWordSize <<- word_size size;
    accounts <- get_accounts;
    sourceBytes <<- f context accounts;
    assert (¬checkSize ∨ offset + size ≤ LENGTH sourceBytes) OutOfBoundsRead;
    bytes <<- take_pad_0 size (DROP offset sourceBytes);
    expandedMemory <<- PAD_RIGHT 0w (minimumWordSize * 32) context.memory;
    newMemory <<- write_memory destOffset bytes expandedMemory;
    expansionCost <<- memory_expansion_cost context.memory newMemory;
    dynamicGas <<- 3 * minimumWordSize + expansionCost;
    newStack <<- DROP 3 context.stack;
    consume_gas dynamicGas;
    spentContext <- get_current_context;
    set_current_context $ spentContext
      with <| stack := newStack; memory := newMemory |>
  od
End

Definition copy_to_memory_def:
  copy_to_memory = copy_to_memory_check F
End

Definition store_to_memory_def:
  store_to_memory f = do
    context <- get_current_context;
    assert (2 ≤ LENGTH context.stack) StackUnderflow;
    byteIndex <<- w2n (EL 0 context.stack);
    value <<- EL 1 context.stack;
    bytes <<- f value;
    newMinSize <<- (word_size $ byteIndex + LENGTH bytes) * 32;
    expandedMemory <<- PAD_RIGHT 0w newMinSize context.memory;
    newMemory <<- write_memory byteIndex bytes expandedMemory;
    expansionCost <<- memory_expansion_cost context.memory newMemory;
    newStack <<- DROP 2 context.stack;
    consume_gas expansionCost;
    spentContext <- get_current_context;
    set_current_context $ spentContext
      with <| stack := newStack; memory := newMemory |>
  od
End

Definition get_current_accesses_def:
  get_current_accesses s = return s.accesses s
End

Definition access_address_def:
  access_address a s =
  let addresses = s.accesses.addresses in
    return
      (fIN a addresses)
      (s with accesses := (s.accesses with addresses := fINSERT a addresses))
End

Definition access_slot_def:
  access_slot x s =
  let storageKeys = s.accesses.storageKeys in
    return
      (fIN x storageKeys)
      (s with accesses := (s.accesses with storageKeys := fINSERT x storageKeys))
End

Definition finish_current_def:
  finish_current returnData = do set_return_data returnData; finish od
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
    valueOffset <<- if call_type = Delegate ∨ call_type = Static then 0 else 1;
    assert (6 + valueOffset ≤ LENGTH context.stack) StackUnderflow;
    gas <<- w2n $ EL 0 context.stack;
    address <<- w2w $ EL 1 context.stack;
    value <<- if valueOffset = 0 then 0 else w2n $ EL 2 context.stack;
    argsOffset <<- w2n $ EL (2 + valueOffset) context.stack;
    argsSize <<- w2n $ EL (3 + valueOffset) context.stack;
    retOffset <<- w2n $ EL (4 + valueOffset) context.stack;
    retSize <<- w2n $ EL (5 + valueOffset) context.stack;
    newStack <<- DROP (6 + valueOffset) context.stack;
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
    toAccountEmpty <<- account_empty toAccount;
    transferCost <<- if call_type = Normal then
      if 0 < value ∧ toAccountEmpty then 25000 else 0
    else 0;
    consume_gas (expansionCost + accessCost + transferCost + positiveValueCost);
    assert (context.callParams.static ⇒ value = 0) WriteInStaticContext;
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
    start_context (call_type = Normal ∨ call_type = Code) F subContext
  od
End

Definition step_create_def:
  step_create two = do
    context <- get_current_context;
    saltOffset <<- if two then 1 else 0;
    assert (3 + saltOffset ≤ LENGTH context.stack) StackUnderflow;
    value <<- w2n $ EL 0 context.stack;
    offset <<- w2n $ EL 1 context.stack;
    size <<- w2n $ EL 2 context.stack;
    salt <<- if two then EL 3 context.stack else 0w;
    senderAddress <<- context.callParams.callee;
    accounts <- get_accounts;
    sender <<- accounts senderAddress;
    nonce <<- sender.nonce;
    rlpSender <<- rlp_bytes $ word_to_bytes senderAddress T;
    rlpNonce <<- rlp_bytes $ MAP n2w $ REVERSE $ n2l 256 $ nonce;
    rlpBytes <<- rlp_list $ rlpSender ++ rlpNonce;
    hash <<- word_of_bytes F (0w:bytes32) $ REVERSE $ Keccak_256_bytes $ rlpBytes;
    newMinSize <<- word_size (offset + size) * 32;
    newMemory <<- PAD_RIGHT 0w newMinSize context.memory;
    newStack <<- DROP (3 + saltOffset) context.stack;
    code <<- TAKE size (DROP offset newMemory);
    address <<-
      if two then w2w $ word_of_bytes F (0w:bytes32) $ REVERSE $ Keccak_256_bytes(
        [n2w 0xff] ++
        word_to_bytes senderAddress T ++
        word_to_bytes salt T ++
        Keccak_256_bytes code)
      else w2w hash;
    access_address address;
    expansionCost <<- memory_expansion_cost context.memory newMemory;
    minimumWordSize <<- word_size size;
    readCodeCost <<- if two then 6 * minimumWordSize else 0;
    newContext <<- context with <| stack := newStack; memory := newMemory |>;
    set_current_context newContext;
    consume_gas (readCodeCost + expansionCost);
    gasLeft <<- context.callParams.gasLimit - context.gasUsed;
    cappedGas <<- gasLeft - gasLeft DIV 64;
    assert (¬context.callParams.static) WriteInStaticContext;
    consume_gas cappedGas;
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
    start_context T T subContext
  od
End

Definition step_sload_def:
  step_sload = do
    context <- get_current_context;
    assert (1 ≤ LENGTH context.stack) StackUnderflow;
    key <<- EL 0 context.stack;
    address <<- context.callParams.callee;
    warm <- access_slot (SK address key);
    dynamicGas <<- if warm then 100 else 2100;
    accounts <- get_accounts;
    word <<- (accounts address).storage key;
    newStack <<- word :: TL context.stack;
    consume_gas dynamicGas;
    spentContext <- get_current_context;
    set_current_context $ spentContext with stack := newStack
  od
End

Definition step_sstore_def:
  step_sstore = do
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
    slotWarm <- access_slot (SK address key);
    baseDynamicGas <<-
      if originalValue = currentValue ∧ currentValue ≠ value
      then if originalValue = 0w then 20000 else 2900
      else 100;
    dynamicGas <<- baseDynamicGas + if slotWarm then 0 else 2100;
    consume_gas dynamicGas;
    spentContext <- get_current_context;
    newStack <<- DROP 2 spentContext.stack;
    newContext <<- spentContext with stack := newStack;
    newContextRefunded <<-
      if value ≠ currentValue then
        if currentValue = originalValue then
          if originalValue ≠ 0w ∧ value = 0w then
            newContext with gasRefund updated_by $+ 4800
          else newContext
        else
          let c =
            if originalValue ≠ 0w then
              if currentValue = 0w then
                newContext with gasRefund updated_by flip $- 4800
              else if value = 0w then
                newContext with gasRefund updated_by $+ 4800
              else newContext
            else newContext
          in
            if value = originalValue then
              if originalValue = 0w then
                c with gasRefund updated_by $+ (20000 - 100)
              else
                c with gasRefund updated_by $+ (5000 - 2100 - 100)
            else c
      else newContext;
    set_current_context newContextRefunded;
    assert (¬context.callParams.static) WriteInStaticContext;
    newStorage <<- (key =+ value) account.storage;
    newAccount <<- account with storage := newStorage;
    update_accounts (address =+ newAccount)
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

Definition step_inst_def:
    step_inst Stop = finish_current []
  ∧ step_inst Add = binop word_add
  ∧ step_inst Mul = binop word_mul
  ∧ step_inst Sub = binop word_sub
  ∧ step_inst Div = binop $ with_zero word_div
  ∧ step_inst SDiv = binop $ with_zero word_quot
  ∧ step_inst Mod = binop $ with_zero word_mod
  ∧ step_inst SMod = binop $ with_zero word_rem
  ∧ step_inst AddMod = stack_op 3 $ modop $+
  ∧ step_inst MulMod = stack_op 3 $ modop $*
  ∧ step_inst Exp = do
      context <- get_current_context;
      assert (2 ≤ LENGTH context.stack) StackUnderflow;
      exponent <<- EL 1 context.stack;
      exponentByteSize <<-
        if exponent = 0w then 0
        else SUC (LOG2 (w2n exponent) DIV 8);
      dynamicGas <<- 50 * exponentByteSize;
      base <<- EL 0 context.stack;
      result <<- word_exp base exponent;
      newStack <<- result :: DROP 2 context.stack;
      consume_gas dynamicGas;
      spentContext <- get_current_context;
      set_current_context $ spentContext with stack := newStack
    od
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
  ∧ step_inst Keccak256 = do
      context <- get_current_context;
      assert (2 ≤ LENGTH context.stack) StackUnderflow;
      offset <<- w2n (EL 0 context.stack);
      size <<- w2n (EL 1 context.stack);
      newMinSize <<- word_size (offset + size) * 32;
      expandedMemory <<- PAD_RIGHT 0w newMinSize context.memory;
      newMemory <<- if 0 < size then expandedMemory else context.memory;
      expansionCost <<- memory_expansion_cost context.memory newMemory;
      dynamicGas <<- 6 * word_size size + expansionCost;
      consume_gas dynamicGas;
      hash <<- word_of_bytes F (0w:bytes32) $ REVERSE $ Keccak_256_bytes $
               TAKE size (DROP offset expandedMemory);
      newStack <<- hash :: DROP 2 context.stack;
      spentContext <- get_current_context;
      set_current_context $ spentContext
        with <| stack := newStack; memory := newMemory |>
    od
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
      spentContext <- get_current_context;
      set_current_context $ spentContext with stack := newStack
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
            let newStack = word_of_bytes F 0w (REVERSE bytes) :: TL context.stack in
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
  ∧ step_inst ExtCodeHash =
      bind get_current_context
      (λcontext.
        ignore_bind (assert (1 ≤ LENGTH context.stack) StackUnderflow) (
          let address = w2w (EL 0 context.stack) in
          bind (access_address address) (λwarm.
          let addressAccessCost = if warm then 100 else 2600 in
          bind get_accounts (λaccounts.
          let code = (accounts address).code in
          (* TODO: handle non-existent or destroyed accounts? (hash = 0) *)
          let hash = word_of_bytes F (0w:bytes32) $ REVERSE $ Keccak_256_bytes $ code in
          let newContext = context with stack := hash :: TL context.stack in
            ignore_bind
              (consume_gas addressAccessCost)
              (set_current_context newContext)))))
  ∧ step_inst BlockHash = do
      tx <- get_tx_params;
      context <- get_current_context;
      assert (1 ≤ LENGTH context.stack) StackUnderflow;
      number <<- w2n $ EL 0 context.stack;
      inRange <<- number < tx.blockNumber ∧ tx.blockNumber - 256 ≤ number;
      index <<- tx.blockNumber - number - 1;
      assert (inRange ⇒ index < LENGTH tx.prevHashes) MissingHashes;
      hash <<- if inRange then EL index tx.prevHashes else 0w;
      newStack <<- hash :: TL context.stack;
      set_current_context (context with stack := newStack)
    od
  ∧ step_inst CoinBase = push_from_tx (λc t a. w2w t.blockCoinBase)
  ∧ step_inst TimeStamp = push_from_tx (λc t a. n2w t.blockTimeStamp)
  ∧ step_inst Number = push_from_tx (λc t a. n2w t.blockNumber)
  ∧ step_inst PrevRandao = push_from_tx (λc t a. t.prevRandao)
  ∧ step_inst GasLimit = push_from_tx (λc t a. n2w t.blockGasLimit)
  ∧ step_inst ChainId = push_from_tx (λc t a. n2w t.chainId)
  ∧ step_inst SelfBalance =
      push_from_tx (λc t a. n2w (a c.callParams.callee).balance)
  ∧ step_inst BaseFee = push_from_tx (λc t a. n2w t.baseFeePerGas)
  ∧ step_inst Pop =
      bind get_current_context
        (λcontext.
          ignore_bind (assert (1 ≤ LENGTH context.stack) StackUnderflow) (
           set_current_context (context with stack := TL context.stack)))
  ∧ step_inst MLoad = do
      context <- get_current_context;
      assert (1 ≤ LENGTH context.stack) StackUnderflow;
      byteIndex <<- w2n (EL 0 context.stack);
      newMinSize <<- word_size (byteIndex + 32) * 32;
      newMemory <<- PAD_RIGHT 0w newMinSize context.memory;
      expansionCost <<- memory_expansion_cost context.memory newMemory;
      word <<- word_of_bytes F 0w $ REVERSE $ TAKE 32 $ DROP byteIndex newMemory;
      newStack <<- word :: TL context.stack;
      consume_gas expansionCost;
      spentContext <- get_current_context;
      set_current_context $ spentContext with
        <| stack := newStack; memory := newMemory |>
    od
  ∧ step_inst MStore = store_to_memory (REVERSE o flip word_to_bytes F)
  ∧ step_inst MStore8 = store_to_memory (SINGL o w2w)
  ∧ step_inst SLoad = step_sload
  ∧ step_inst SStore = step_sstore
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
  ∧ step_inst Gas = push_from_ctxt (λc. n2w $
      c.callParams.gasLimit - c.gasUsed - static_gas Gas)
  ∧ step_inst JumpDest = return ()
  ∧ step_inst (Push n ws) =
      bind get_current_context
        (λcontext.
          let word = word_of_bytes F 0w (REVERSE ws) in
          let newStack = word :: context.stack in
          ignore_bind (assert (LENGTH newStack ≤ stack_limit) StackOverflow) (
          set_current_context (context with stack := newStack)))
  ∧ step_inst (Dup n) =
      bind (get_current_context)
        (λcontext.
          ignore_bind (assert (n < LENGTH context.stack) StackUnderflow) (
            let word = EL n context.stack in
            let newStack = word :: context.stack in
            ignore_bind (assert (LENGTH newStack ≤ stack_limit) StackOverflow) (
            set_current_context (context with stack := newStack))))
  ∧ step_inst (Swap n) =
      bind get_current_context
        (λcontext.
          ignore_bind (assert (SUC n < LENGTH context.stack) StackUnderflow) (
            let top = HD context.stack in
            let swap = EL n (TL context.stack) in
            let ignored = TAKE n (TL context.stack) in
            let rest = DROP (SUC n) (TL context.stack) in
            let newStack = [swap] ++ ignored ++ [top] ++ rest in
              set_current_context (context with stack := newStack)))
  ∧ step_inst (Log n) = do
      context <- get_current_context;
      assert (¬context.callParams.static) WriteInStaticContext;
      assert (2 + n ≤ LENGTH context.stack) StackUnderflow;
      offset <<- w2n $ EL 0 context.stack;
      size <<- w2n $ EL 1 context.stack;
      newMinSize <<- word_size (offset + size) * 32;
      newMemory <<- PAD_RIGHT 0w newMinSize context.memory;
      expansionCost <<- memory_expansion_cost context.memory newMemory;
      dynamicGas <<- 375 * n + 8 * size + expansionCost;
      consume_gas dynamicGas;
      logger <<- context.callParams.callee;
      topics <<- TAKE n (DROP 2 context.stack);
      data <<- TAKE size (DROP offset newMemory);
      event <<- <| logger := logger; topics := topics; data := data |>;
      newContext <<- context with
        <| memory := newMemory; logs := event :: context.logs |>;
      set_current_context newContext
    od
  ∧ step_inst Create = step_create F
  ∧ step_inst Call = step_call Normal
  ∧ step_inst CallCode = step_call Code
  ∧ step_inst Return = do
      context <- get_current_context;
      assert (2 ≤ LENGTH context.stack) StackUnderflow;
      offset <<- w2n $ EL 0 context.stack;
      size <<- w2n $ EL 1 context.stack;
      newMinSize <<- word_size (offset + size) * 32;
      expandedMemory <<- PAD_RIGHT 0w newMinSize context.memory;
      returnData <<- TAKE size (DROP offset expandedMemory);
      expansionCost <<- memory_expansion_cost context.memory expandedMemory;
      consume_gas expansionCost;
      finish_current returnData
    od
  ∧ step_inst DelegateCall = step_call Delegate
  ∧ step_inst Create2 = step_create T
  ∧ step_inst StaticCall = step_call Static
  ∧ step_inst Revert = do
      context <- get_current_context;
      assert (2 ≤ LENGTH context.stack) StackUnderflow;
      offset <<- w2n $ EL 0 context.stack;
      size <<- w2n $ EL 1 context.stack;
      newStack <<- DROP 2 context.stack;
      newMinSize <<- word_size (offset + size) * 32;
      newMemory <<- PAD_RIGHT 0w newMinSize context.memory;
      expansionCost <<- memory_expansion_cost context.memory newMemory;
      consume_gas expansionCost;
      returnData <<- TAKE size (DROP offset newMemory);
      newContext <<- context with <|
                       stack := newStack;
                       memory := newMemory;
                       returnData := returnData
                     |>;
      set_current_context newContext;
      revert
    od
  ∧ step_inst SelfDestruct = do
      context <- get_current_context;
      assert (1 ≤ LENGTH context.stack) StackUnderflow;
      assert (¬context.callParams.static) WriteInStaticContext;
      address <<- w2w $ EL 0 context.stack;
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
      | NONE => do
          consume_gas (context.callParams.gasLimit - context.gasUsed);
          set_return_data [];
          revert
        od
      | SOME op => do
          step_inst op;
          consume_gas (static_gas op);
          if is_call op then return () else inc_pc (LENGTH (opcode op))
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
  let (gasLimit, gasUsed, refund, logs, returnData) =
    if NULL t.contexts ∨ ¬NULL (TL t.contexts)
    then (0, 0, 0, [], MAP (n2w o ORD) "not exactly one remaining context")
    else let ctxt = HD t.contexts in
      (ctxt.callParams.gasLimit, ctxt.gasUsed,
       ctxt.gasRefund, ctxt.logs, ctxt.returnData) in
  let gasLeft = gasLimit - gasUsed in
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
