Theory vfmExecution
Ancestors
  arithmetic
  blake2f bn254 bls12381 sha2 ripemd160[ignore_grammar] secp256k1
  vfmTypes vfmRoot vfmContext
Libs
  monadsyntax

(* TODO: move *)
Definition modexp_def:
  modexp (b:num) (e:num) (m: num) (a:num) =
  if e = 0n then (a MOD m) else
  if EVEN e then
    modexp ((b * b) MOD m) (DIV2 e) m a
  else
    modexp b (PRE e) m ((b * a) MOD m)
Termination
  WF_REL_TAC`measure (FST o SND)`
  \\ rw[DIV2_def]
End

Theorem modexp_exp:
  !b e m a. 0 < m ⇒ modexp b e m a = (a * b ** e) MOD m
Proof
  recInduct modexp_ind
  \\ rpt strip_tac
  \\ simp[Once modexp_def]
  \\ IF_CASES_TAC
  \\ gs[EVEN_EXISTS, DIV2_def]
  \\ rw[] >- gs[GSYM EXP_EXP_MULT]
  \\ Cases_on`e` \\ gs[EXP]
QED
(* -- *)

Definition ecrecover_def:
  ecrecover hash v r s : address option =
  if ¬(v = 27 ∨ v = 28) then NONE else
  if ¬(0 < r ∧ r < secp256k1N) then NONE else
  if ¬(0 < s ∧ s < secp256k1N) then NONE else
  if ¬(fleg (secp256k1$weierstrassEquation r) = 1) then NONE else let
    yParity = v - 27;
    point = recoverPoint r s yParity hash
  in if SND (SND point) = 0 then NONE else let
    keyBytes = pointToUncompressedBytes point;
    addrBytes = DROP 12 $ Keccak_256_w64 keyBytes
  in SOME $ word_of_bytes T 0w addrBytes
End

Definition ecadd_def:
  ecadd a b =
  if ¬(bn254$validAffine a ∧ bn254$validAffine b) then NONE
  else SOME $ bn254$addAffine a b
End

Definition ecmul_def:
  ecmul p s =
  if ¬(bn254$validAffine p) then NONE
  else SOME $ bn254$mulAffine p s
End

Definition ecpairing_def:
  ecpairing data res =
  if LENGTH data < 192 then
    if NULL data then SOME res else NONE
  else let
    px = num_of_be_bytes $ TAKE 32 data; data = DROP 32 data;
    py = num_of_be_bytes $ TAKE 32 data; data = DROP 32 data;
    p = (px, py);
    in if ¬bn254$validAffine p then NONE else let
    qxi = num_of_be_bytes $ TAKE 32 data; data = DROP 32 data;
    qx1 = num_of_be_bytes $ TAKE 32 data; data = DROP 32 data;
    qyi = num_of_be_bytes $ TAKE 32 data; data = DROP 32 data;
    qy1 = num_of_be_bytes $ TAKE 32 data; data = DROP 32 data;
    qx = (qx1, qxi);
    qy = (qy1, qyi);
  in
    if ¬bn254$validAffineF2 (qx, qy) then NONE else
    if bn254$mulAffine p bn254n ≠ (0,0) then NONE else
    if bn254$mulAffineF2 (qx, qy) bn254n ≠ (bn254$f2zero, bn254$f2zero) then NONE else
      ecpairing data
        (if (px ≠ 0 ∨ py ≠ 0) ∧ (qx ≠ bn254$f2zero ∨ qy ≠ bn254$f2zero)
         then bn254$poly12_mul res (bn254$miller_loop qx qy p)
         else res)
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’ \\ rw[]
End

Definition lookup_transient_storage_def:
  lookup_transient_storage a (t: transient_storage) = t a
End

Definition update_transient_storage_def:
  update_transient_storage a s (t: transient_storage) = (a =+ s) t
End

Definition b2w_def[simp]:
  b2w T = 1w ∧ b2w F = 0w
End

Definition with_zero_def:
  with_zero f x y = if y = 0w then 0w else f x y
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

Definition account_already_created_def:
  account_already_created a =
    ¬(a.nonce = 0 ∧ NULL a.code ∧ storage_empty a.storage)
End

Definition memory_cost_def:
  memory_cost byteSize =
  let wordSize = word_size byteSize in
  (wordSize * wordSize) DIV 512 +
    (memory_cost_per_word * wordSize)
End

Definition memory_expansion_cost_def:
  memory_expansion_cost oldSize newMinSize =
  let newSize = MAX oldSize newMinSize in
    memory_cost newSize - memory_cost oldSize
End

Theorem memory_expansion_cost_0[simp]:
  memory_expansion_cost x 0 = 0
Proof
  rw[memory_expansion_cost_def]
QED

Definition call_has_value_def:
  call_has_value op = (op = Call ∨ op = CallCode)
End

Definition max_expansion_range_def:
  max_expansion_range (o1, s1) (o2, s2:num) =
  let v1 = if s1 = 0 then 0 else o1 + s1 in
  let v2 = if s2 = 0 then 0 else o2 + s2 in
    if v1 < v2 then (o2, s2) else (o1, s1)
End

Definition call_gas_def:
  call_gas value gas gasLeft memoryCost otherCost =
  let stipend = if value = 0n then 0 else call_stipend in
  let gas = if gasLeft < memoryCost + otherCost then gas
            else MIN gas (
              let left = gasLeft - memoryCost - otherCost in
                left - (left DIV 64)
              ) in
    (gas + otherCost, gas + stipend)
End

Definition address_for_create2_def:
  address_for_create2 (address: address) (salt: bytes32) (code: byte list) : address =
  w2w $ word_of_bytes T (0w: bytes32) $ Keccak_256_w64 $
    [0xffw] ++ word_to_bytes address T ++
    word_to_bytes salt T ++ Keccak_256_w64 code
End

Datatype:
  exception =
  | OutOfGas
  | StackOverflow
  | StackUnderflow
  | InvalidJumpDest
  | WriteInStaticContext
  | OutOfBoundsRead
  | AddressCollision
  | InvalidContractPrefix
  | InvalidParameter
  | KZGProofError
  | Reverted
  (* semantic invariants/assumptions (not EVM exceptions) *)
  | OutsideDomain (address + storage_key + address)
  | Unimplemented
  | Impossible
End

Definition vfm_abort_def[simp]:
  vfm_abort (SOME (OutsideDomain _)) = T ∧
  vfm_abort (SOME Unimplemented) = T ∧
  vfm_abort (SOME Impossible) = T ∧
  vfm_abort _ = F
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

Definition reraise_def:
  reraise e s = (INR e, s) : α execution_result
End

Definition handle_def:
  handle f h s : α execution_result =
  case f s
    of (INR e, s) => h e s
     | otherwise => otherwise
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
    return (FST (HD s.contexts)) s
End

Definition set_current_context_def:
  set_current_context c s =
  if s.contexts = [] then
    fail Impossible s
  else
    return () (s with contexts := (c, SND(HD s.contexts))::(TL s.contexts))
End

Definition get_num_contexts_def:
  get_num_contexts s = return (LENGTH s.contexts) s
End

Definition push_context_def:
  push_context crb s = return () $ s with contexts updated_by CONS crb
End

Definition pop_context_def:
  pop_context s =
  if s.contexts = [] then fail Impossible s
  else return (HD s.contexts) (s with contexts updated_by TL)
End

Definition get_tx_params_def:
  get_tx_params s = return s.txParams s
End

Definition get_accounts_def:
  get_accounts s = return s.rollback.accounts s
End

Definition update_accounts_def:
  update_accounts f s = return () $
    s with rollback updated_by (λr. r with accounts updated_by f)
End

Definition get_tStorage_def:
  get_tStorage s = return s.rollback.tStorage s
End

Definition set_tStorage_def:
  set_tStorage x s = return () $
    s with rollback updated_by (λr. r with tStorage := x)
End

Definition get_rollback_def:
  get_rollback s = return s.rollback s
End

Definition set_rollback_def:
  set_rollback r s = return () $ s with rollback := r
End

Definition get_original_def:
  get_original s =
    if s.contexts = [] then
      fail Impossible s
    else
      return (SND (LAST s.contexts)).accounts s
End

Definition set_last_accounts_def:
  set_last_accounts a ls =
  let lc = LAST ls in
    SNOC (FST lc, SND lc with accounts := a)
         (FRONT ls)
End

Definition set_original_def:
  set_original a s =
    if s.contexts = [] then
      fail Impossible s
    else
      return () $ s with contexts updated_by
        (set_last_accounts a)
End

Definition get_gas_left_def:
  get_gas_left = do
    context <- get_current_context;
    return $ context.msgParams.gasLimit - context.gasUsed
  od
End

Definition get_callee_def:
  get_callee = do
    context <- get_current_context;
    return context.msgParams.callee
  od
End

Definition get_caller_def:
  get_caller = do
    context <- get_current_context;
    return context.msgParams.caller
  od
End

Definition get_value_def:
  get_value = do
    context <- get_current_context;
    return context.msgParams.value
  od
End

Definition get_output_to_def:
  get_output_to = do
    context <- get_current_context;
    return context.msgParams.outputTo
  od
End

Definition get_return_data_def:
  get_return_data = do
    context <- get_current_context;
    return context.returnData
  od
End

Definition get_return_data_check_def:
  get_return_data_check offset size = do
    data <- get_return_data;
    assert (offset + size ≤ LENGTH data) OutOfBoundsRead;
    return data
  od
End

Definition set_return_data_def:
  set_return_data rd = do
    context <- get_current_context;
    newContext <<- context with returnData := rd;
    set_current_context newContext
  od
End

Definition get_static_def:
  get_static = do
    context <- get_current_context;
    return context.msgParams.static
  od
End

Definition get_code_def:
  get_code address = do
    accounts <- get_accounts;
    return $ (lookup_account address accounts).code
  od
End

Definition get_current_code_def:
  get_current_code = do
    context <- get_current_context;
    return $ context.msgParams.code
  od
End

Definition get_call_data_def:
  get_call_data = do
    context <- get_current_context;
    return $ context.msgParams.data
  od
End

Definition set_jump_dest_def:
  set_jump_dest jumpDest = do
    context <- get_current_context;
    set_current_context $
      context with jumpDest := jumpDest
  od
End

Definition push_logs_def:
  push_logs ls = do
    context <- get_current_context;
    set_current_context $ context with logs updated_by (flip APPEND ls)
  od
End

Definition update_gas_refund_def:
  update_gas_refund (add, sub) = do
    context <- get_current_context;
    set_current_context $
      context with <|
        addRefund updated_by ($+ add);
        subRefund updated_by ($+ sub)
      |>
  od
End

Definition consume_gas_def:
  consume_gas n =
  do
    context <- get_current_context;
    newContext <<- context with gasUsed := context.gasUsed + n;
    assert (newContext.gasUsed ≤ context.msgParams.gasLimit) OutOfGas;
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

Definition pop_stack_def:
  pop_stack n =
  do
    context <- get_current_context;
    stack <<- context.stack;
    assert (n ≤ LENGTH stack) StackUnderflow;
    set_current_context $ context with stack := DROP n stack;
    return $ TAKE n stack
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

Definition add_to_delete_def:
  add_to_delete a s =
  return () $
    s with rollback updated_by
      (λr. r with toDelete updated_by CONS a)
End

Definition set_domain_def:
  set_domain d s = return () (s with msdomain := d)
End

Definition domain_check_def:
  domain_check err check add cont s =
  case s.msdomain of
  | Enforce d =>
      if check d then cont s else fail (OutsideDomain err) s
  | Collect d =>
      ignore_bind (set_domain (Collect (add d))) cont s
End

Definition access_address_def:
  access_address a =
  domain_check (INL a)
    (λd. fIN a d.addresses)
    (λd. d with addresses updated_by fINSERT a)
  (λs. let addresses = s.rollback.accesses.addresses in
       let newAccesses = s.rollback.accesses with addresses := fINSERT a addresses in
       let newRollback = s.rollback with accesses := newAccesses in
         return
           (if fIN a addresses then warm_access_cost else cold_access_cost)
           (s with rollback := newRollback))
End

Definition access_slot_def:
  access_slot x =
  domain_check (INR (INL x))
    (λd. fIN x d.storageKeys)
    (λd. d with storageKeys updated_by fINSERT x)
  (λs. let storageKeys = s.rollback.accesses.storageKeys in
       let newAccesses = s.rollback.accesses with storageKeys := fINSERT x storageKeys in
       let newRollback = s.rollback with accesses := newAccesses in
         return
           (if fIN x storageKeys then warm_access_cost else cold_sload_cost)
           (s with rollback := newRollback))
End

Definition ensure_storage_in_domain_def:
  ensure_storage_in_domain a =
  domain_check (INR (INR a))
    (λd. fIN a d.fullStorages)
    (λd. d with fullStorages updated_by fINSERT a)
  (return ())
End

Definition zero_warm_def:
  zero_warm accessCost = if accessCost > warm_access_cost then accessCost else 0n
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
       ; expand_by := MAX oldSize newMinSize - oldSize |>
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

Definition copy_to_memory_def:
  copy_to_memory gas offset sourceOffset size getSource = do
    minimumWordSize <<- word_size size;
    (xOffset, xSize) <<-
      if getSource = NONE
      then max_expansion_range (offset, size) (sourceOffset, size)
      else (offset, size);
    mx <- memory_expansion_info xOffset xSize;
    dynamicGas <<- memory_copy_cost * minimumWordSize + mx.cost;
    consume_gas $ gas + dynamicGas;
    bytes <- case getSource of SOME f => do
      sourceBytes <- f;
      expand_memory mx.expand_by;
      return $ take_pad_0 size (DROP sourceOffset sourceBytes)
    od | _ => do
      expand_memory mx.expand_by;
      read_memory sourceOffset size
    od;
    write_memory offset bytes;
  od
End

Definition write_storage_def:
  write_storage address key value =
  update_accounts (λaccounts.
    let account = lookup_account address accounts in
    let newAccount = account with storage updated_by (update_storage key value);
    in update_account address newAccount accounts)
End

Definition write_transient_storage_def:
  write_transient_storage address key value = do
    tStorage <- get_tStorage;
    storage <<- lookup_transient_storage address tStorage;
    set_tStorage $ update_transient_storage
      address (update_storage key value storage) tStorage
  od
End

Definition assert_not_static_def:
  assert_not_static = do
    static <- get_static;
    assert (¬static) WriteInStaticContext
  od
End

Definition transfer_value_def:
  transfer_value (fromAddress: address) toAddress value accounts =
  if value = 0 ∨ fromAddress = toAddress then accounts else
    let sender = lookup_account fromAddress accounts in
    let recipient = lookup_account toAddress accounts in
    let newSender = sender with balance updated_by flip $- value in
    let newRecipient = recipient with balance updated_by $+ value in
      update_account toAddress newRecipient $
      update_account fromAddress newSender $ accounts
End

Definition increment_nonce_def:
  increment_nonce address accounts =
  let account = lookup_account address accounts in
    update_account address (account with nonce updated_by SUC) accounts
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

Definition step_monop_def:
  step_monop op f = do
    args <- pop_stack 1;
    consume_gas (static_gas op);
    push_stack $ f (EL 0 args);
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

Definition step_context_def:
  step_context op f = do
    consume_gas $ static_gas op;
    context <- get_current_context;
    push_stack $ f context
  od
End

Definition step_msgParams_def:
  step_msgParams op f = step_context op (λc. f c.msgParams)
End

Definition step_txParams_def:
  step_txParams op f = do
    consume_gas $ static_gas op;
    txParams <- get_tx_params;
    push_stack $ f txParams
  od
End

Definition step_exp_def:
  step_exp = do
    args <- pop_stack 2;
    base <<- EL 0 args;
    exponent <<- EL 1 args;
    exponentByteSize <<-
      if exponent = 0w then 0
      else SUC (LOG2 (w2n exponent) DIV 8);
    dynamicGas <<- exp_per_byte_cost * exponentByteSize;
    consume_gas $ static_gas Exp + dynamicGas;
    result <<- word_exp base exponent;
    push_stack $ result
  od
End

Definition step_keccak256_def:
  step_keccak256 = do
    args <- pop_stack 2;
    offset <<- w2n (EL 0 args);
    size <<- w2n (EL 1 args);
    mx <- memory_expansion_info offset size;
    dynamicGas <<- keccak256_per_word_cost * word_size size + mx.cost;
    consume_gas $ static_gas Keccak256 + dynamicGas;
    expand_memory mx.expand_by;
    data <- read_memory offset size;
    hash <<- word_of_bytes T (0w:bytes32) $ Keccak_256_w64 $ data;
    push_stack hash
  od
End

Definition step_sload_def:
  step_sload transient = do
    args <- pop_stack 1;
    key <<- EL 0 args;
    address <- get_callee;
    accessCost <- if transient then return warm_access_cost
                  else access_slot (SK address key);
    consume_gas $ accessCost;
    storage <- if transient then do
      tStorage <- get_tStorage;
      return $ lookup_transient_storage address tStorage
    od else do
      accounts <- get_accounts;
      return $ (lookup_account address accounts).storage
    od;
    word <<- lookup_storage key storage;
    push_stack word
  od
End

Definition step_sstore_gas_consumption_def:
  step_sstore_gas_consumption address key value = do
    gasLeft <- get_gas_left;
    assert (call_stipend < gasLeft) OutOfGas;
    accounts <- get_accounts;
    currentValue <<- lookup_storage key (lookup_account address accounts).storage;
    original <- get_original;
    originalValue <<- lookup_storage key (lookup_account address original).storage;
    accessCost <- access_slot (SK address key);
    baseDynamicGas <<-
      if originalValue = currentValue ∧ currentValue ≠ value
      then if originalValue = 0w
           then storage_set_cost
           else storage_update_cost - cold_sload_cost
      else warm_access_cost;
    dynamicGas <<- baseDynamicGas + zero_warm accessCost;
    refundUpdates <<-
      if currentValue ≠ value then
        let storageSetRefund =
          if originalValue = value then
            if originalValue = 0w then
              storage_set_cost - warm_access_cost
            else
              storage_update_cost - cold_sload_cost - warm_access_cost
          else 0
        in
          if originalValue ≠ 0w ∧ currentValue ≠ 0w ∧ value = 0w then
            (storageSetRefund + storage_clear_refund, 0)
          else if originalValue ≠ 0w ∧ currentValue = 0w then
            (storageSetRefund, storage_clear_refund)
          else (storageSetRefund, 0)
      else (0, 0);
    update_gas_refund refundUpdates;
    consume_gas dynamicGas;
  od
End

Definition step_sstore_def:
  step_sstore transient = do
    args <- pop_stack 2;
    key <<- EL 0 args;
    value <<- EL 1 args;
    address <- get_callee;
    if transient then consume_gas warm_access_cost
    else step_sstore_gas_consumption address key value;
    assert_not_static;
    (if transient then write_transient_storage
                  else write_storage)
      address key value
  od
End

Definition step_balance_def:
  step_balance = do
    args <- pop_stack 1;
    address <<- w2w $ EL 0 args;
    accessCost <- access_address address;
    consume_gas $ static_gas Balance + accessCost;
    accounts <- get_accounts;
    balance <<- n2w $ (lookup_account address accounts).balance;
    push_stack balance
  od
End

Definition step_call_data_load_def:
  step_call_data_load = do
    args <- pop_stack 1;
    index <<- w2n $ EL 0 args;
    consume_gas $ static_gas CallDataLoad;
    callData <- get_call_data;
    bytes <<- take_pad_0 32 (DROP index callData);
    push_stack $ word_of_bytes F 0w (REVERSE bytes)
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

Definition step_return_data_copy_def:
  step_return_data_copy = do
    args <- pop_stack 3;
    offset <<- w2n $ EL 0 args;
    sourceOffset <<- w2n $ EL 1 args;
    size <<- w2n $ EL 2 args;
    copy_to_memory (static_gas ReturnDataCopy)
    offset sourceOffset size (SOME $ get_return_data_check sourceOffset size)
  od
End

Definition step_ext_code_size_def:
  step_ext_code_size = do
    args <- pop_stack 1;
    address <<- w2w $ EL 0 args;
    accessCost <- access_address address;
    consume_gas $ static_gas ExtCodeSize + accessCost;
    accounts <- get_accounts;
    code <<- (lookup_account address accounts).code;
    push_stack $ n2w (LENGTH code)
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
      offset sourceOffset size (SOME $ get_code address)
  od
End

Definition step_ext_code_hash_def:
  step_ext_code_hash = do
    args <- pop_stack 1;
    address <<- w2w $ EL 0 args;
    accessCost <- access_address address;
    consume_gas $ static_gas ExtCodeHash + accessCost;
    accounts <- get_accounts;
    account <<- lookup_account address accounts;
    hash <<- if account_empty account then 0w
             else word_of_bytes T (0w:bytes32) $ Keccak_256_w64 $
                  account.code;
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

Definition step_blob_hash_def:
  step_blob_hash = do
    args <- pop_stack 1;
    index <<- w2n $ EL 0 args;
    consume_gas $ static_gas BlobHash;
    tx <- get_tx_params;
    hash <<- if index < LENGTH tx.blobHashes
             then EL index tx.blobHashes
             else 0w;
    push_stack hash
  od
End

Definition step_self_balance_def:
  step_self_balance = do
    consume_gas $ static_gas SelfBalance;
    accounts <- get_accounts;
    address <- get_callee;
    balance <<- n2w (lookup_account address accounts).balance;
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
    bytes <<- if op = MStore8 then [w2w value]
              else REVERSE $ word_to_bytes value F;
    mx <- memory_expansion_info offset size;
    consume_gas $ static_gas op + mx.cost;
    expand_memory mx.expand_by;
    write_memory offset bytes;
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
    consume_gas $ static_gas JumpI;
    set_jump_dest jumpDest
  od
End

Definition step_push_def:
  step_push n ws = do
    consume_gas $ static_gas $ Push n ws;
    push_stack $ word_of_bytes F 0w $ REVERSE ws
  od
End

Definition step_pop_def:
  step_pop = do
    pop_stack 1;
    consume_gas $ static_gas Pop
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

Definition step_log_def:
  step_log n = do
    args <- pop_stack $ 2 + n;
    offset <<- w2n $ EL 0 args;
    size <<- w2n $ EL 1 args;
    topics <<- DROP 2 args;
    mx <- memory_expansion_info offset size;
    dynamicGas <<- log_topic_cost * n + log_data_cost * size + mx.cost;
    consume_gas $ (static_gas $ Log n) + dynamicGas;
    expand_memory mx.expand_by;
    assert_not_static;
    address <- get_callee;
    data <- read_memory offset size;
    event <<- <| logger := address; topics := topics; data := data |>;
    push_logs [event]
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

Definition step_invalid_def:
  step_invalid = do
    gasLeft <- get_gas_left;
    consume_gas gasLeft;
    set_return_data [];
    revert
  od
End

Definition step_self_destruct_def:
  step_self_destruct = do
    args <- pop_stack 1;
    address <<- w2w $ EL 0 args;
    accessCost <- access_address address;
    senderAddress <- get_callee;
    accounts <- get_accounts;
    sender <<- lookup_account senderAddress accounts;
    balance <<- sender.balance;
    beneficiaryEmpty <<- account_empty $ lookup_account address accounts;
    transferCost <<- if 0 < balance ∧ beneficiaryEmpty
                     then self_destruct_new_account_cost else 0;
    consume_gas $ static_gas SelfDestruct + zero_warm accessCost + transferCost;
    assert_not_static;
    update_accounts $ transfer_value senderAddress address balance;
    original <- get_original;
    originalContract <<- lookup_account senderAddress original;
    if account_empty originalContract then do
      update_accounts $
        update_account senderAddress (sender with balance := 0);
      add_to_delete senderAddress
    od else return ();
    finish
  od
End

Definition inc_pc_def:
  inc_pc = do
    context <- get_current_context;
    set_current_context $ context with pc updated_by SUC
  od
End

Definition abort_unuse_def:
  abort_unuse n = do
    unuse_gas n;
    push_stack $ b2w F;
    inc_pc
  od
End

Definition abort_create_exists_def:
  abort_create_exists senderAddress = do
    update_accounts $ increment_nonce senderAddress;
    push_stack $ b2w F;
    inc_pc
  od
End

Definition proceed_create_def:
  proceed_create senderAddress address value code cappedGas =
  do
    update_accounts $ increment_nonce senderAddress;
    subContextTx <<- <|
        from     := senderAddress
      ; to       := SOME address
      ; value    := value
      ; gasLimit := cappedGas
      ; data     := []
      (* unused: for concreteness *)
      ; nonce := 0; gasPrice := 0; accessList := []
      ; blobVersionedHashes := []
      ; maxFeePerGas := NONE; maxFeePerBlobGas := NONE
      ; authorizationList := []
    |>;
    rollback <- get_rollback;
    original <- get_original;
    set_original $ update_account address empty_account_state original;
    update_accounts $
      transfer_value senderAddress address value o
      increment_nonce address;
    push_context
      (initial_context address code F (Code address) subContextTx, rollback)
  od
End

Definition step_create_def:
  step_create two = do
    args <- pop_stack (if two then 4 else 3);
    value <<- w2n $ EL 0 args;
    offset <<- w2n $ EL 1 args;
    size <<- w2n $ EL 2 args;
    salt <<- if two then EL 3 args else 0w;
    mx <- memory_expansion_info offset size;
    staticGas <<- static_gas (if two then Create2 else Create);
    callDataWords <<- word_size size;
    initCodeCost <<- init_code_word_cost * callDataWords;
    readCodeCost <<- if two then keccak256_per_word_cost * callDataWords else 0;
    consume_gas $ staticGas + initCodeCost + readCodeCost + mx.cost;
    expand_memory mx.expand_by;
    code <- read_memory offset size;
    senderAddress <- get_callee;
    accounts <- get_accounts;
    sender <<- lookup_account senderAddress accounts;
    nonce <<- sender.nonce;
    address <<- if two
                then address_for_create2 senderAddress salt code
                else address_for_create senderAddress nonce;
    assert (LENGTH code ≤ 2 * max_code_size) OutOfGas;
    access_address address;
    gasLeft <- get_gas_left;
    cappedGas <<- gasLeft - gasLeft DIV 64;
    consume_gas cappedGas;
    assert_not_static;
    set_return_data [];
    sucDepth <- get_num_contexts;
    ensure_storage_in_domain address;
    toCreate <<- lookup_account address accounts;
    if sender.balance < value ∨
       SUC nonce ≥ 2 ** 64 ∨
       sucDepth > 1024
    then abort_unuse cappedGas
    else if account_already_created toCreate
    then abort_create_exists senderAddress
    else proceed_create senderAddress address value code cappedGas
  od
End

Definition abort_call_value_def:
  abort_call_value stipend = do
    push_stack $ b2w F;
    set_return_data [];
    unuse_gas stipend;
    inc_pc
  od
End

Definition precompile_ecrecover_def:
  precompile_ecrecover = do
    input <- get_call_data;
    consume_gas $ 3000;
    hash <<- word_of_bytes T (0w:bytes32) $ take_pad_0 32 input;
    v <<- num_of_be_bytes $ take_pad_0 32 (DROP 32 input);
    r <<- num_of_be_bytes $ take_pad_0 32 (DROP 64 input);
    s <<- num_of_be_bytes $ take_pad_0 32 (DROP 96 input);
    case ecrecover hash v r s of NONE => finish | SOME addr => do
      set_return_data $ PAD_LEFT 0w 32 $ word_to_bytes addr T;
      finish
    od
  od
End

Definition precompile_identity_def:
  precompile_identity = do
    input <- get_call_data;
    dynamic_gas <<- 3 * word_size (LENGTH input);
    consume_gas (15 + dynamic_gas);
    set_return_data input;
    finish
  od
End

Overload num_from_input_words = “λz ls.
  l2n 256 $ REVERSE $ MAP w2n $ take_pad_0 z ls”

Overload bitlength = “λn. SUC (LOG2 (MAX 1 n))”

Definition precompile_modexp_def:
  precompile_modexp = do
    inputs <- get_call_data;
    bSize <<- w2n $ word_of_bytes T (0w:bytes32) $ take_pad_0 32 inputs;
    eSize <<- w2n $ word_of_bytes T (0w:bytes32) $ take_pad_0 32 (DROP 32 inputs);
    mSize <<- w2n $ word_of_bytes T (0w:bytes32) $ take_pad_0 32 (DROP 64 inputs);
    maxLength <<- MAX bSize mSize;
    words <<- (maxLength + 7) DIV 8;
    multiplicationComplexity <<- words * words;
    restInputs <<- DROP 96 inputs;
    eHead <<- num_from_input_words (MIN 32 eSize) $ DROP bSize restInputs;
    iterationCount <<-
      if eSize ≤ 32 then
        if eHead = 0 then 0n else bitlength eHead - 1
      else 8 * (eSize - 32) + (bitlength (w2n (n2w eHead: bytes32)) - 1);
    calculatedIterationCount <<- MAX iterationCount 1;
    cost <<- multiplicationComplexity * calculatedIterationCount;
    dynamicGas <<- MAX 200 (cost DIV 3);
    consume_gas dynamicGas;
    m <<- num_from_input_words mSize $ DROP (bSize + eSize) restInputs;
    set_return_data $
      if bSize = 0 ∧ mSize = 0 then []
      else if m = 0 then REPLICATE mSize 0w
      else let
        nums = MAP w2n $ take_pad_0 (bSize + eSize + mSize) $ restInputs;
        b = l2n 256 $ REVERSE $ TAKE bSize nums;
        e = l2n 256 $ REVERSE $ TAKE eSize $ DROP bSize nums
      in REVERSE $ PAD_RIGHT 0w mSize $ MAP n2w $ n2l 256 $ modexp b e m 1;
    finish
  od
End

Definition precompile_sha2_256_def:
  precompile_sha2_256 = do
    input <- get_call_data;
    hsh <<- SHA_256_bytes input;
    dynamic_gas <<- 12 * word_size (LENGTH input);
    consume_gas (60 + dynamic_gas);
    set_return_data $ word_to_bytes hsh T;
    finish
    od
End

Definition precompile_ripemd_160_def:
  precompile_ripemd_160 = do
    input <- get_call_data;
    wordCount <<- word_size $ LENGTH input;
    consume_gas $ 600 + 120 * wordCount;
    case ripemd160$RIPEMD_160_bytes input of
      NONE => fail OutOfGas
    | SOME hsh => do
        set_return_data $ PAD_LEFT 0w 32 $ word_to_bytes hsh T;
        finish
      od
  od
End

Definition precompile_ecadd_def:
  precompile_ecadd = do
    input <- get_call_data;
    consume_gas $ 150;
    ax <<- num_of_be_bytes $ take_pad_0 32 input;
    ay <<- num_of_be_bytes $ take_pad_0 32 (DROP 32 input);
    bx <<- num_of_be_bytes $ take_pad_0 32 (DROP 64 input);
    by <<- num_of_be_bytes $ take_pad_0 32 (DROP 96 input);
    case ecadd (ax, ay) (bx, by) of
      NONE => fail OutOfGas
    | SOME (x, y) => do
      set_return_data $
        PAD_LEFT 0w 32 (num_to_be_bytes x) ++
        PAD_LEFT 0w 32 (num_to_be_bytes y);
      finish
    od
  od
End

Definition precompile_ecmul_def:
  precompile_ecmul = do
    input <- get_call_data;
    consume_gas $ 6000;
    px <<- num_of_be_bytes $ take_pad_0 32 input;
    py <<- num_of_be_bytes $ take_pad_0 32 (DROP 32 input);
    s <<- num_of_be_bytes $ take_pad_0 32 (DROP 64 input);
    case ecmul (px, py) s of
      NONE => fail OutOfGas
    | SOME (x, y) => do
      set_return_data $
        PAD_LEFT 0w 32 (num_to_be_bytes x) ++
        PAD_LEFT 0w 32 (num_to_be_bytes y);
      finish
    od
  od
End

Definition precompile_ecpairing_def:
  precompile_ecpairing = do
    input <- get_call_data;
    len <<- LENGTH input;
    consume_gas $ 34000 * (len DIV 192) + 45000;
    if len MOD 192 ≠ 0 then fail OutOfGas else
    case ecpairing input bn254$poly12_one of NONE => fail OutOfGas | SOME res => do
      set_return_data $ PAD_LEFT 0w 32
        [if bn254$final_exponentiation res = bn254$poly12_one then 1w else 0w];
      finish
    od
  od
End

Definition precompile_blake2f_def:
  precompile_blake2f = do
    input <- get_call_data;
    if LENGTH input ≠ 213 then fail InvalidParameter else do
      rounds <<- num_of_be_bytes $ TAKE 4 input; input <<- DROP 4 input;
      hs <<- MAP (word_of_bytes F 0w) $ chunks 8 $ TAKE 64 input; input <<- DROP 64 input;
      ms <<- MAP (word_of_bytes F 0w) $ chunks 8 $ TAKE 128 input; input <<- DROP 128 input;
      t0 <<- word_of_bytes F 0w $ TAKE 8 input; input <<- DROP 8 input;
      t1 <<- word_of_bytes F 0w $ TAKE 8 input; input <<- DROP 8 input;
      flag <<- HD input;
      consume_gas $ rounds;
      if ¬(flag = 0w ∨ flag = 1w) then fail InvalidParameter else do
        set_return_data $ blake2f rounds hs ms t0 t1 flag;
        finish
      od
    od
  od
End

Definition point_eval_output_def:
  point_eval_output =
    (PAD_LEFT 0w 32 $ num_to_be_bytes 4096) ++
    (PAD_LEFT 0w 32 $ num_to_be_bytes
     52435875175126190479447740508185965837690552500527637822603658699938581184513)
End

Definition precompile_point_eval_def:
  precompile_point_eval = do
    input <- get_call_data;
    if LENGTH input ≠ 192 then fail KZGProofError else do
      versionedHash <<- TAKE 32 input; input <<- DROP 32 input;
      z <<- num_of_be_bytes $ TAKE 32 input; input <<- DROP 32 input;
      y <<- num_of_be_bytes $ TAKE 32 input; input <<- DROP 32 input;
      commitment_bytes <<- TAKE 48 input; input <<- DROP 48 input;
      proof_bytes <<- TAKE 48 input;
      consume_gas 50000;
      computedHash <<- word_to_bytes (SHA_256_bytes commitment_bytes) T;
      computedVersionedHash <<- versioned_hash_version_kzg :: DROP 1 computedHash;
      assert (versionedHash = computedVersionedHash) KZGProofError;
      assert (z < bls12381$bls12381n ∧ y < bls12381$bls12381n) KZGProofError;
      commitment_opt <<- bls12381$g1_decompress commitment_bytes;
      proof_opt <<- bls12381$g1_decompress proof_bytes;
      case (commitment_opt, proof_opt) of
      | (SOME commitment, SOME proof) => do
          assert (bls12381$verify_kzg_proof commitment z y proof) KZGProofError;
          set_return_data point_eval_output;
          finish
        od
      | _ => fail KZGProofError
    od
  od
End

Definition precompile_bls_g1add_def:
  precompile_bls_g1add = do
    input <- get_call_data;
    consume_gas 375;
    case bls12381$bls_g1add input of
      NONE => fail OutOfGas
    | SOME result => do set_return_data result; finish od
  od
End

Definition precompile_bls_g1msm_def:
  precompile_bls_g1msm = do
    input <- get_call_data;
    k <<- LENGTH input DIV 160;
    gas <<- k * 12000 * bls12381$g1_msm_discount k DIV 1000;
    consume_gas gas;
    case bls12381$bls_g1msm input of
      NONE => fail OutOfGas
    | SOME result => do set_return_data result; finish od
  od
End

Definition precompile_bls_g2add_def:
  precompile_bls_g2add = do
    input <- get_call_data;
    consume_gas 600;
    case bls12381$bls_g2add input of
      NONE => fail OutOfGas
    | SOME result => do set_return_data result; finish od
  od
End

Definition precompile_bls_g2msm_def:
  precompile_bls_g2msm = do
    input <- get_call_data;
    k <<- LENGTH input DIV 288;
    gas <<- k * 22500 * bls12381$g2_msm_discount k DIV 1000;
    consume_gas gas;
    case bls12381$bls_g2msm input of
      NONE => fail OutOfGas
    | SOME result => do set_return_data result; finish od
  od
End

Definition precompile_bls_pairing_def:
  precompile_bls_pairing = do
    input <- get_call_data;
    k <<- LENGTH input DIV 384;
    gas <<- 32600 * k + 37700;
    consume_gas gas;
    case bls12381$bls_pairing input of
      NONE => fail OutOfGas
    | SOME result => do set_return_data result; finish od
  od
End

Definition precompile_bls_map_fp_to_g1_def:
  precompile_bls_map_fp_to_g1 = do
    input <- get_call_data;
    consume_gas 5500;
    case bls12381$bls_map_fp_to_g1 input of
      NONE => fail OutOfGas
    | SOME result => do set_return_data result; finish od
  od
End

Definition precompile_bls_map_fp2_to_g2_def:
  precompile_bls_map_fp2_to_g2 = do
    input <- get_call_data;
    consume_gas 23800;
    case bls12381$bls_map_fp2_to_g2 input of
      NONE => fail OutOfGas
    | SOME result => do set_return_data result; finish od
  od
End

Definition dispatch_precompiles_def:
  dispatch_precompiles (a: address) =
    if a = 0x1w then precompile_ecrecover
    else if a = 0x2w then precompile_sha2_256
    else if a = 0x3w then precompile_ripemd_160
    else if a = 0x4w then precompile_identity
    else if a = 0x5w then precompile_modexp
    else if a = 0x6w then precompile_ecadd
    else if a = 0x7w then precompile_ecmul
    else if a = 0x8w then precompile_ecpairing
    else if a = 0x9w then precompile_blake2f
    else if a = 0xaw then precompile_point_eval
    else if a = 0xbw then precompile_bls_g1add
    else if a = 0xcw then precompile_bls_g1msm
    else if a = 0xdw then precompile_bls_g2add
    else if a = 0xew then precompile_bls_g2msm
    else if a = 0xfw then precompile_bls_pairing
    else if a = 0x10w then precompile_bls_map_fp_to_g1
    else if a = 0x11w then precompile_bls_map_fp2_to_g2
    else fail Impossible
End

Definition proceed_call_def:
  proceed_call op sender address value
    argsOffset argsSize code stipend
    outputTo = do
    rollback <- get_rollback;
    data <- read_memory argsOffset argsSize;
    if op ≠ CallCode (* otherwise to := sender *) ∧ 0 < value then
      update_accounts $ transfer_value sender address value
    else return ();
    caller <- get_caller;
    callValue <- get_value;
    callee <<- if op = CallCode ∨ op = DelegateCall
               then sender else address;
    subContextTx <<- <|
        from     := if op = DelegateCall then caller else sender
      ; to       := SOME callee
      ; value    := if op = DelegateCall then callValue else value
      ; gasLimit := stipend
      ; data     := data
      (* unused: for concreteness *)
      ; nonce := 0; gasPrice := 0; accessList := []
      ; blobVersionedHashes := []
      ; maxFeePerGas := NONE; maxFeePerBlobGas := NONE
      ; authorizationList := []
    |>;
    static <- get_static;
    subStatic <<- (op = StaticCall ∨ static);
    context <<- initial_context callee code subStatic outputTo subContextTx;
    push_context (context, rollback);
    if fIN address precompile_addresses
    then dispatch_precompiles address
    else return ()
  od
End

Definition step_call_def:
  step_call op = do
    valueOffset <<- if call_has_value op then 1 else 0;
    args <- pop_stack (6 + valueOffset);
    gas <<- w2n $ EL 0 args;
    address <<- w2w $ EL 1 args;
    value <<- if 0 < valueOffset then w2n $ EL 2 args else 0;
    argsOffset <<- w2n $ EL (2 + valueOffset) args;
    argsSize <<- w2n $ EL (3 + valueOffset) args;
    retOffset <<- w2n $ EL (4 + valueOffset) args;
    retSize <<- w2n $ EL (5 + valueOffset) args;
    (offset, size) <<- max_expansion_range
      (argsOffset, argsSize) (retOffset, retSize);
    mx <- memory_expansion_info offset size;
    accessCost <- access_address address;
    positiveValueCost <<- if 0 < value then call_value_cost else 0;
    accounts <- get_accounts;
    toAccount <<- lookup_account address accounts;
    (code, delegateCost) <- case get_delegate toAccount.code of
               NONE => return (toAccount.code, 0)
             | SOME delegate => do
                 cost <- access_address delegate;
                 return ((lookup_account delegate accounts).code, cost)
               od;
    createCost <<- if op = Call ∧ 0 < value ∧ account_empty toAccount
                   then new_account_cost else 0;
    gasLeft <- get_gas_left;
    (dynamicGas, stipend) <<- call_gas value gas gasLeft mx.cost $
                                accessCost + positiveValueCost + createCost + delegateCost;
    consume_gas $ static_gas op + dynamicGas + mx.cost;
    if op = Call ∧ 0 < value then assert_not_static else return ();
    expand_memory mx.expand_by;
    sender <- get_callee;
    if (lookup_account sender accounts).balance < value
    then abort_call_value stipend
    else do
      set_return_data [];
      sucDepth <- get_num_contexts;
      if sucDepth > 1024
      then abort_unuse stipend
      else proceed_call op sender address value
             argsOffset argsSize code stipend
             (Memory <| offset := retOffset; size := retSize |>)
    od
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
  ∧ step_inst AddMod = step_modop AddMod $+
  ∧ step_inst MulMod = step_modop MulMod $*
  ∧ step_inst Exp = step_exp
  ∧ step_inst SignExtend = step_binop SignExtend sign_extend
  ∧ step_inst LT = step_binop LT (λx y. b2w (w2n x < w2n y))
  ∧ step_inst GT = step_binop GT (λx y. b2w (w2n x > w2n y))
  ∧ step_inst SLT = step_binop SLT (λx y. b2w $ word_lt x y)
  ∧ step_inst SGT = step_binop SGT (λx y. b2w $ word_gt x y)
  ∧ step_inst Eq = step_binop Eq (λx y. b2w (x = y))
  ∧ step_inst IsZero = step_monop IsZero (λx. b2w (x = 0w))
  ∧ step_inst And = step_binop And word_and
  ∧ step_inst Or = step_binop Or word_or
  ∧ step_inst XOr = step_binop XOr word_xor
  ∧ step_inst Not = step_monop Not word_1comp
  ∧ step_inst Byte = step_binop Byte (λi w. if w2n i < 32 then w2w $ get_byte i w T else 0w)
  ∧ step_inst ShL = step_binop ShL (λn w. word_lsl w (w2n n))
  ∧ step_inst ShR = step_binop ShR (λn w. word_lsr w (w2n n))
  ∧ step_inst SAR = step_binop SAR (λn w. word_asr w (w2n n))
  ∧ step_inst Keccak256 = step_keccak256
  ∧ step_inst Address = step_msgParams Address (λc. w2w c.callee)
  ∧ step_inst Balance = step_balance
  ∧ step_inst Origin = step_txParams Origin (λt. w2w t.origin)
  ∧ step_inst Caller = step_msgParams Caller (λc. w2w c.caller)
  ∧ step_inst CallValue = step_msgParams CallValue (λc. n2w c.value)
  ∧ step_inst CallDataLoad = step_call_data_load
  ∧ step_inst CallDataSize = step_msgParams CallDataSize (λc. n2w (LENGTH c.data))
  ∧ step_inst CallDataCopy =
      step_copy_to_memory CallDataCopy (SOME get_call_data)
  ∧ step_inst CodeSize = step_msgParams CodeSize (λc. n2w (LENGTH c.code))
  ∧ step_inst CodeCopy = step_copy_to_memory CodeCopy (SOME get_current_code)
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
  ∧ step_inst BlobHash = step_blob_hash
  ∧ step_inst BlobBaseFee = step_txParams BlobBaseFee (λt. n2w t.baseFeePerBlobGas)
  ∧ step_inst Pop = step_pop
  ∧ step_inst MLoad = step_mload
  ∧ step_inst MStore = step_mstore MStore
  ∧ step_inst MStore8 = step_mstore MStore8
  ∧ step_inst SLoad = step_sload F
  ∧ step_inst SStore = step_sstore F
  ∧ step_inst Jump = step_jump
  ∧ step_inst JumpI = step_jumpi
  ∧ step_inst PC = step_context PC (λc. n2w c.pc)
  ∧ step_inst MSize = step_context MSize (λc. n2w $ LENGTH c.memory)
  ∧ step_inst Gas = step_context Gas
                      (λc. n2w $ c.msgParams.gasLimit - c.gasUsed)
  ∧ step_inst TLoad = step_sload T
  ∧ step_inst TStore = step_sstore T
  ∧ step_inst MCopy = step_copy_to_memory MCopy NONE
  ∧ step_inst JumpDest = consume_gas $ static_gas JumpDest
  ∧ step_inst (Push n ws) = step_push n ws
  ∧ step_inst (Dup n) = step_dup n
  ∧ step_inst (Swap n) = step_swap n
  ∧ step_inst (Log n) = step_log n
  ∧ step_inst Create = step_create F
  ∧ step_inst Call = step_call Call
  ∧ step_inst CallCode = step_call CallCode
  ∧ step_inst Return = step_return T
  ∧ step_inst DelegateCall = step_call DelegateCall
  ∧ step_inst Create2 = step_create T
  ∧ step_inst StaticCall = step_call StaticCall
  ∧ step_inst Revert = step_return F
  ∧ step_inst Invalid = step_invalid
  ∧ step_inst SelfDestruct = step_self_destruct
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

Definition inc_pc_or_jump_def:
  inc_pc_or_jump op =
  if is_call op then return () else do
    n <<- LENGTH (opcode op);
    context <- get_current_context;
    case context.jumpDest of
    | NONE => set_current_context $ context with pc := context.pc + n
    | SOME pc => do
        code <<- context.msgParams.code;
        parsed <<- context.msgParams.parsed;
        assert (pc < LENGTH code ∧
                FLOOKUP parsed pc = SOME JumpDest) InvalidJumpDest;
        set_current_context $
          context with <| pc := pc; jumpDest := NONE |>
      od
  od
End

Definition pop_and_incorporate_context_def:
  pop_and_incorporate_context success = do
    calleeGasLeft <- get_gas_left;
    callee_rb <- pop_context;
    callee <<- FST callee_rb;
    unuse_gas calleeGasLeft;
    if success then do
      push_logs callee.logs;
      update_gas_refund (callee.addRefund, callee.subRefund)
    od else
      set_rollback (SND callee_rb)
  od
End

Definition handle_create_def:
  handle_create e = do
    code <- get_return_data;
    outputTo <- get_output_to;
    case (e, outputTo) of
    | (NONE, Code address) => do
      codeLen <<- LENGTH code;
      codeGas <<- code_deposit_cost * codeLen;
      assert (case code of h::_ => h ≠ n2w 0xef | _ => T) InvalidContractPrefix;
      consume_gas codeGas;
      assert (codeLen ≤ max_code_size) OutOfGas;
      update_accounts $ (λaccounts.
        update_account address
          (lookup_account address accounts with code := code)
          accounts);
      reraise e
    od | _ => reraise e
  od
End

Definition handle_exception_def:
  handle_exception e = do
    success <<- (e = NONE);
    if ¬success ∧ e ≠ SOME Reverted then do
      gasLeft <- get_gas_left;
      consume_gas gasLeft;
      set_return_data [];
    od else return ();
    n <- get_num_contexts;
    if n ≤ 1 then reraise e else do
    output <- get_return_data;
    outputTo <- get_output_to;
    pop_and_incorporate_context success;
    inc_pc;
    case outputTo of
    | Code address =>
        if success then do
          set_return_data [];
          push_stack $ w2w address
        od else do
          set_return_data output;
          push_stack $ b2w F
        od
    | Memory r => do
        set_return_data output;
        push_stack $ b2w success;
        write_memory r.offset (TAKE r.size output)
      od
    od
  od
End

Definition handle_step_def:
  handle_step e =
  if vfm_abort e then reraise e else
  handle (handle_create e) handle_exception
End

Definition step_def:
  step = handle do
    context <- get_current_context;
    code <<- context.msgParams.code;
    parsed <<- context.msgParams.parsed;
    if LENGTH code ≤ context.pc
    then step_inst Stop else
    do case FLOOKUP parsed context.pc of
      | NONE => step_inst Invalid
      | SOME op => do step_inst op; inc_pc_or_jump op od
    od
  od handle_step
End

Definition run_def:
  run s = OWHILE (ISL o FST) (step o SND) (INL (), s)
End

Datatype:
  transaction_result =
  <| gasUsed  : num
   ; logs     : event list
   ; output   : byte list
   ; result   : exception option
   ; domain   : domain_mode
   |>
End

Definition process_deletions_def:
  process_deletions [] acc = acc ∧
  process_deletions (a::as) acc =
  process_deletions as (update_account a empty_account_state acc)
End

Definition post_transaction_accounting_def:
  post_transaction_accounting blk tx result acc t =
  let (gasLimit, gasUsed, addRefund, subRefund, logs, returnData) =
    if NULL t.contexts ∨ ¬NULL (TL t.contexts)
    then (0, 0, 0, 0, [], MAP (n2w o ORD) "not exactly one remaining context")
    else let ctxt = FST $ HD t.contexts in
      (ctxt.msgParams.gasLimit, ctxt.gasUsed,
       ctxt.addRefund, ctxt.subRefund, ctxt.logs, ctxt.returnData) in
  let gasLeft = gasLimit - gasUsed in
  let txGasUsed = tx.gasLimit - gasLeft in
  let gasRefund = if result ≠ NONE then 0
                  else MIN (txGasUsed DIV 5) (addRefund - subRefund) in
  let tokens = call_data_tokens tx.data in
  let floor_cost = base_cost + floor_call_data_cost * tokens in
  let totalGasUsed = MAX (txGasUsed - gasRefund) floor_cost in
  let refundEther = (tx.gasLimit - totalGasUsed) * tx.gasPrice in
  let priorityFeePerGas = tx.gasPrice - blk.baseFeePerGas in
  let transactionFee = totalGasUsed * priorityFeePerGas in
  let accounts = if result = NONE
                 then process_deletions t.rollback.toDelete t.rollback.accounts
                 else acc in
  let sender = lookup_account tx.from accounts in
  let feeRecipient = lookup_account blk.coinBase accounts in
  let newAccounts =
    update_account tx.from
      (sender with balance updated_by $+ refundEther) $
    update_account blk.coinBase
      (feeRecipient with balance updated_by $+ transactionFee)
    accounts in
  let logs = if result = NONE then logs else [] in
  let tr = <| gasUsed := totalGasUsed;
              logs := logs;
              result := result;
              output := returnData;
              domain := t.msdomain |> in
  (tr, newAccounts)
End

Definition run_create_def:
  run_create dom static chainId prevHashes blk accounts tx =
  case initial_state dom static chainId prevHashes blk accounts tx of
    NONE => NONE
  | SOME s => SOME $
    let crb = HD s.contexts in
    let ctxt = FST crb in
    let calleeAddress = ctxt.msgParams.callee in
    if IS_SOME tx.to then
      INR $ (s.rollback.accounts, s with rollback updated_by
                                   (λr. r with accounts updated_by
             transfer_value tx.from calleeAddress tx.value),
             if fIN calleeAddress precompile_addresses
             then SOME calleeAddress else NONE)
    else
      let accounts = s.rollback.accounts in
      let callee = lookup_account calleeAddress accounts in
      if account_already_created callee then
        INL $ post_transaction_accounting blk tx (SOME AddressCollision) accounts
              (s with contexts := [
                (ctxt with gasUsed := ctxt.msgParams.gasLimit,
                 SND crb)
               ])
      else
        INR $ (accounts, s with <|
            rollback updated_by (λr. r with accounts updated_by (
              transfer_value tx.from calleeAddress tx.value o
              increment_nonce calleeAddress
            ));
            contexts updated_by (
              set_last_accounts $
              update_account calleeAddress empty_account_state
                (SND crb).accounts
            )|>, NONE)
End

Definition run_transaction_def:
  run_transaction dom static chainId prevHashes blk accounts tx =
  case run_create dom static chainId prevHashes blk accounts tx of
     | SOME (INL result) => SOME result
     | SOME (INR (acc, s1, precomp)) => (case
          case precomp
            of NONE => run s1
             | SOME addr => SOME $
                 handle (dispatch_precompiles addr) handle_step s1
       of
       | SOME (INR r, s2) => SOME $
          post_transaction_accounting blk tx r acc s2
       | _ => NONE)
     | _ => NONE
End

Definition update_beacon_block_def:
  update_beacon_block prevHashes b (accounts: evm_accounts) =
  let beacon_addr = 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02w in
  let buffer_length = 8191n in
  let timestamp_idx = b.timeStamp MOD buffer_length in
  let root_idx = timestamp_idx + buffer_length in
  let a = lookup_account beacon_addr accounts in
  let s0 = a.storage in
  let s1 = update_storage (n2w timestamp_idx) (n2w b.timeStamp) s0 in
  let s2 = update_storage (n2w root_idx) (b.parentBeaconBlockRoot) s1 in
  let accounts1 = update_account beacon_addr (a with storage := s2) accounts in
  if b.number = 0 ∨ prevHashes = [] then accounts1 else
  let blockhash_addr = 0x0000F90827F1C53a10cb7A02335B175320002935w in
  let slot = (b.number - 1) MOD buffer_length in
  let parent_hash = HD prevHashes in
  let a2 = lookup_account blockhash_addr accounts1 in
  let s3 = update_storage (n2w slot) parent_hash a2.storage in
  update_account blockhash_addr (a2 with storage := s3) accounts1
End

Definition process_withdrawal_def:
  process_withdrawal w (a, dm) =
  let addr = w.withdrawalAddress in
  OPTION_BIND
    (case dm
      of Collect d =>
           SOME $ Collect $ d with addresses updated_by fINSERT addr
       | Enforce d =>
           if fIN addr d.addresses then SOME $ Enforce d else NONE)
    (λdm. SOME (
      update_account addr
        (lookup_account addr a with balance updated_by
         (+) (w.withdrawalAmount * 10 ** 9)) a,
      dm))
End

Definition process_withdrawals_def:
  process_withdrawals [] x = SOME x ∧
  process_withdrawals (w::ws) x =
  OPTION_BIND (process_withdrawal w x)
    (process_withdrawals ws)
End

Definition is_deposit_event_def:
  is_deposit_event (e: event) ⇔
    e.logger = deposit_contract_address ∧
    ¬NULL e.topics ∧
    HD e.topics = deposit_event_topic
End

Definition parse_deposit_request_def:
  parse_deposit_request (data: byte list) =
  if LENGTH data < 576 then NONE else
  let pubkey_offset = w2n (word_of_bytes T (0w:bytes32) (TAKE 32 data)) in
  let withdrawal_creds_offset = w2n (word_of_bytes T (0w:bytes32) (TAKE 32 (DROP 32 data))) in
  let amount_offset = w2n (word_of_bytes T (0w:bytes32) (TAKE 32 (DROP 64 data))) in
  let signature_offset = w2n (word_of_bytes T (0w:bytes32) (TAKE 32 (DROP 96 data))) in
  let index_offset = w2n (word_of_bytes T (0w:bytes32) (TAKE 32 (DROP 128 data))) in
  let pubkey = TAKE 48 (DROP (pubkey_offset + 32) data) in
  let withdrawal_creds = TAKE 32 (DROP (withdrawal_creds_offset + 32) data) in
  let amount = TAKE 8 (DROP (amount_offset + 32) data) in
  let signature = TAKE 96 (DROP (signature_offset + 32) data) in
  let index = TAKE 8 (DROP (index_offset + 32) data) in
  SOME (pubkey ++ withdrawal_creds ++ amount ++ signature ++ index)
End

Definition parse_deposit_events_def:
  parse_deposit_events ([] : event list) = SOME [] ∧
  parse_deposit_events (e::es) =
    case parse_deposit_request e.data of
      NONE => NONE
    | SOME req =>
        case parse_deposit_events es of
          NONE => NONE
        | SOME reqs => SOME (req :: reqs)
End

Definition extract_deposit_requests_def:
  extract_deposit_requests logs =
  parse_deposit_events (FILTER is_deposit_event logs)
End

Definition read_withdrawal_request_def:
  read_withdrawal_request storage idx =
  let base = 4 + idx * 3 in
  let slot0 = lookup_storage (n2w base) storage in
  let slot1 = lookup_storage (n2w (base + 1)) storage in
  let slot2 = lookup_storage (n2w (base + 2)) storage in
  let source_addr = DROP 12 (word_to_bytes slot0 T) in
  let pubkey_part1 = word_to_bytes slot1 T in
  let slot2_bytes = word_to_bytes slot2 T in
  let pubkey_part2 = TAKE 16 slot2_bytes in
  let amount = REVERSE (TAKE 8 (DROP 16 slot2_bytes)) in
  source_addr ++ pubkey_part1 ++ pubkey_part2 ++ amount
End

Definition dequeue_withdrawal_requests_def:
  dequeue_withdrawal_requests accounts =
  let contract = lookup_account withdrawal_request_contract accounts in
  let storage = contract.storage in
  let head = w2n (lookup_storage 2w storage) in
  let tail = w2n (lookup_storage 3w storage) in
  let dequeue_count = MIN (tail - head) max_withdrawal_requests_per_block in
  let requests = GENLIST (λi. read_withdrawal_request storage (head + i)) dequeue_count in
  let new_head = head + dequeue_count in
  let old_excess = w2n (lookup_storage 0w storage) in
  let add_count = w2n (lookup_storage 1w storage) in
  let new_excess = if old_excess + add_count > target_withdrawal_requests_per_block
                   then old_excess + add_count - target_withdrawal_requests_per_block
                   else 0 in
  let storage1 = update_storage 0w (n2w new_excess) storage in
  let storage2 = update_storage 1w 0w storage1 in
  let storage3 = if new_head = tail
                 then update_storage 3w 0w (update_storage 2w 0w storage2)
                 else update_storage 2w (n2w new_head) storage2 in
  let updated_contract = contract with storage := storage3 in
  let updated_accounts = update_account withdrawal_request_contract updated_contract accounts in
  (requests, updated_accounts)
End

Definition read_consolidation_request_def:
  read_consolidation_request storage idx =
  let base = 4 + idx * 4 in
  let slot0 = lookup_storage (n2w base) storage in
  let slot1 = lookup_storage (n2w (base + 1)) storage in
  let slot2 = lookup_storage (n2w (base + 2)) storage in
  let slot3 = lookup_storage (n2w (base + 3)) storage in
  let source_addr = DROP 12 (word_to_bytes slot0 T) in
  let source_pubkey_part1 = word_to_bytes slot1 T in
  let slot2_bytes = word_to_bytes slot2 T in
  let source_pubkey_part2 = TAKE 16 slot2_bytes in
  let target_pubkey_part1 = DROP 16 slot2_bytes in
  let target_pubkey_part2 = word_to_bytes slot3 T in
  source_addr ++ source_pubkey_part1 ++ source_pubkey_part2 ++
  target_pubkey_part1 ++ target_pubkey_part2
End

Definition dequeue_consolidation_requests_def:
  dequeue_consolidation_requests accounts =
  let contract = lookup_account consolidation_request_contract accounts in
  let storage = contract.storage in
  let head = w2n (lookup_storage 2w storage) in
  let tail = w2n (lookup_storage 3w storage) in
  let dequeue_count = MIN (tail - head) max_consolidation_requests_per_block in
  let requests = GENLIST (λi. read_consolidation_request storage (head + i)) dequeue_count in
  let new_head = head + dequeue_count in
  let old_excess = w2n (lookup_storage 0w storage) in
  let add_count = w2n (lookup_storage 1w storage) in
  let new_excess = if old_excess + add_count > target_consolidation_requests_per_block
                   then old_excess + add_count - target_consolidation_requests_per_block
                   else 0 in
  let storage1 = update_storage 0w (n2w new_excess) storage in
  let storage2 = update_storage 1w 0w storage1 in
  let storage3 = if new_head = tail
                 then update_storage 3w 0w (update_storage 2w 0w storage2)
                 else update_storage 2w (n2w new_head) storage2 in
  let updated_contract = contract with storage := storage3 in
  let updated_accounts = update_account consolidation_request_contract updated_contract accounts in
  (requests, updated_accounts)
End

Definition compute_requests_hash_def:
  compute_requests_hash (deposits: byte list list)
                        (withdrawals: byte list list)
                        (consolidations: byte list list) =
  let deposit_data = FLAT deposits in
  let deposit_hash = if NULL deposit_data then []
                     else word_to_bytes (SHA_256_bytes (0x00w :: deposit_data)) T in
  let withdrawal_data = FLAT withdrawals in
  let withdrawal_hash = if NULL withdrawal_data then []
                        else word_to_bytes (SHA_256_bytes (0x01w :: withdrawal_data)) T in
  let consolidation_data = FLAT consolidations in
  let consolidation_hash = if NULL consolidation_data then []
                           else word_to_bytes (SHA_256_bytes (0x02w :: consolidation_data)) T in
  let all_hashes = deposit_hash ++ withdrawal_hash ++ consolidation_hash in
  SHA_256_bytes all_hashes
End

Definition expected_base_fee_def:
  expected_base_fee parent_base_fee parent_gas_limit parent_gas_used =
    let parent_gas_target = parent_gas_limit DIV elasticity_multiplier in
    if parent_gas_used = parent_gas_target then parent_base_fee
    else if parent_gas_used > parent_gas_target then
      let gas_used_delta = parent_gas_used - parent_gas_target in
      let base_fee_delta = parent_base_fee * gas_used_delta
                           DIV parent_gas_target
                           DIV base_fee_max_change_denominator in
      let base_fee_delta = MAX base_fee_delta 1 in
      parent_base_fee + base_fee_delta
    else
      let gas_used_delta = parent_gas_target - parent_gas_used in
      let base_fee_delta = parent_base_fee * gas_used_delta
                           DIV parent_gas_target
                           DIV base_fee_max_change_denominator in
      parent_base_fee - base_fee_delta
End

Definition block_invalid_def:
  block_invalid p rs deposits withdrawals consolidations b ⇔
    let blobGasUsed = SUM (MAP total_blob_gas b.transactions) in
    let gasUsed = SUM (MAP (λr. r.gasUsed) rs) in
    let excessBlobGas = (p.excessBlobGas + p.blobGasUsed)
                        - target_blob_gas_per_block in
    let requestsHash = compute_requests_hash deposits withdrawals consolidations in
    let expectedBaseFee = expected_base_fee p.baseFeePerGas p.gasLimit p.gasUsed in
    let expectedWithdrawalsRoot =
          word_of_bytes T 0w (withdrawals_root b.withdrawals) in
    ¬(min_gas_limit ≤ b.gasLimit ∧
      b.baseFeePerGas = expectedBaseFee ∧
      blobGasUsed ≤ max_blob_gas_per_block ∧
      blobGasUsed = b.blobGasUsed ∧
      gasUsed = b.gasUsed ∧
      excessBlobGas = b.excessBlobGas ∧
      requestsHash = b.requestsHash ∧
      expectedWithdrawalsRoot = b.withdrawalsRoot)
End

Definition run_block_def:
  run_block dom chainId prevHashes parent accounts b =
  OPTION_BIND (
    FOLDL
      (λx tx.
         OPTION_BIND x (λ(ls, a, dom).
           OPTION_MAP (λ(r, a). (SNOC r ls, a, r.domain)) $
           run_transaction dom F chainId prevHashes b a tx))
      (SOME ([], update_beacon_block prevHashes b accounts, dom))
      b.transactions )
  (λ(rs, a, d).
    let all_logs = FLAT (MAP (λr. r.logs) rs) in
    OPTION_BIND (extract_deposit_requests all_logs) (λdeposits.
      let (withdrawals, a1) = dequeue_withdrawal_requests a in
      let (consolidations, a2) = dequeue_consolidation_requests a1 in
      if block_invalid parent rs deposits withdrawals consolidations b then NONE
      else
        OPTION_BIND (process_withdrawals b.withdrawals (a2, d))
          (λ(a, d). SOME (rs, a, d))))
End

Definition run_blocks_def:
  run_blocks dom chainId prevHashes parent accounts bs =
  FOLDL
    (λx b.
      OPTION_BIND x (λ(ls, h, p, a, dom).
        OPTION_MAP (λ(rs, a, dom). (SNOC rs ls, b.hash::h, b, a, dom)) $
          run_block dom chainId h p a b))
    (SOME ([], prevHashes, parent, accounts, dom))
    bs
End

Definition run_block_to_hash_def:
  run_block_to_hash dom chainId prevHashes parent accounts blk =
  case run_block dom chainId prevHashes parent accounts blk
    of NONE => NONE
     | SOME (rs, s, d) => SOME (state_root s, d)
End

Definition run_blocks_to_hash_def:
  run_blocks_to_hash dom chainId prevHashes parent accounts bs =
  case run_blocks dom chainId prevHashes parent accounts bs
    of NONE => NONE
     | SOME (rs, hs, p, s, d) => SOME (state_root s, d)
End
