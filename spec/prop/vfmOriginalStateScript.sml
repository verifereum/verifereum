Theory vfmOriginalState
Ancestors
  arithmetic list rich_list pair option sum While
  vfmContext vfmExecution
Libs
  monadsyntax

(* Compatibility reference for the former bottom-frame account layout.
   Unchanged instructions and all frame settlement handlers are shared with
   vfmExecution. The extra originalAccounts field is ignored by this reference. *)

val () = monadsyntax.enable_monad "evm_execution";
val () = monadsyntax.enable_monadsyntax();

Definition stack_original_get_original_def:
  stack_original_get_original s =
    if s.contexts = [] then
      fail Impossible s
    else
      return (SND (LAST s.contexts)).accounts s
End

Definition stack_original_set_original_def:
  stack_original_set_original a s =
    if s.contexts = [] then
      fail Impossible s
    else
      return () $ s with contexts updated_by
        (set_last_accounts a)
End

Definition stack_original_step_sstore_gas_consumption_def:
  stack_original_step_sstore_gas_consumption address key value = do
    gasLeft <- get_gas_left;
    assert (call_stipend < gasLeft) OutOfGas;
    accounts <- get_accounts;
    currentValue <<- lookup_storage key (lookup_account address accounts).storage;
    original <- stack_original_get_original;
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

Definition stack_original_step_sstore_def:
  stack_original_step_sstore transient = do
    args <- pop_stack 2;
    key <<- EL 0 args;
    value <<- EL 1 args;
    address <- get_callee;
    if transient then consume_gas warm_access_cost
    else stack_original_step_sstore_gas_consumption address key value;
    assert_not_static;
    (if transient then write_transient_storage
                  else write_storage)
      address key value
  od
End

Definition stack_original_step_self_destruct_def:
  stack_original_step_self_destruct = do
    args <- pop_stack 1;
    address <<- w2w $ EL 0 args;
    accessCost <- access_address address;
    senderAddress <- get_callee;
    set_return_data [];
    accounts <- get_accounts;
    sender <<- lookup_account senderAddress accounts;
    balance <<- sender.balance;
    beneficiaryEmpty <<- account_empty $ lookup_account address accounts;
    transferCost <<- if 0 < balance ∧ beneficiaryEmpty
                     then self_destruct_new_account_cost else 0;
    consume_gas $ static_gas SelfDestruct + zero_warm accessCost + transferCost;
    assert_not_static;
    update_accounts $ transfer_value senderAddress address balance;
    original <- stack_original_get_original;
    originalContract <<- lookup_account senderAddress original;
    if account_empty originalContract then do
      update_accounts $
        update_account senderAddress (sender with balance := 0);
      add_to_delete senderAddress
    od else return ();
    finish
  od
End

Definition stack_original_proceed_create_def:
  stack_original_proceed_create senderAddress address value code cappedGas =
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
    original <- stack_original_get_original;
    stack_original_set_original $ update_account address empty_account_state original;
    update_accounts $
      transfer_value senderAddress address value o
      increment_nonce address;
    push_context
      (initial_context address code F (Code address) subContextTx, rollback)
  od
End

Definition stack_original_step_create_def:
  stack_original_step_create two = do
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
    gasLeft <- get_gas_left;
    cappedGas <<- gasLeft - gasLeft DIV 64;
    consume_gas cappedGas;
    assert_not_static;
    set_return_data [];
    sucDepth <- get_num_contexts;
    if sender.balance < value ∨
       SUC nonce ≥ 2 ** 64 ∨
       sucDepth > 1024
    then abort_unuse cappedGas
    else do
      access_address address;
      ensure_storage_in_domain address;
      toCreate <<- lookup_account address accounts;
      if account_already_created toCreate
      then abort_create_exists senderAddress
      else stack_original_proceed_create senderAddress address value code cappedGas
    od
  od
End

Definition stack_original_step_inst_def:
  stack_original_step_inst op =
    case op of
      SStore => stack_original_step_sstore F
    | SelfDestruct => stack_original_step_self_destruct
    | Create => stack_original_step_create F
    | Create2 => stack_original_step_create T
    | _ => step_inst op
End

Definition stack_original_step_def:
  stack_original_step = handle do
    context <- get_current_context;
    code <<- context.msgParams.code;
    parsed <<- context.msgParams.parsed;
    case FLOOKUP parsed context.pc of
    | SOME op => do stack_original_step_inst op; inc_pc_or_jump op od
    | NONE =>
        if LENGTH code ≤ context.pc
        then stack_original_step_inst Stop
        else stack_original_step_inst Invalid
  od handle_step
End

Definition stack_original_run_def:
  stack_original_run s = OWHILE (ISL o FST) (stack_original_step o SND) (INL (), s)
End

Definition stack_original_run_call_def:
  stack_original_run_call es =
    OWHILE (λ(r, s). ISL r ∧ LENGTH s.contexts ≥ LENGTH es.contexts)
           (stack_original_step o SND) (INL (), es)
End

Definition stack_original_run_within_frame_def:
  stack_original_run_within_frame es =
    OWHILE (λ(r, s). ISL r ∧ LENGTH s.contexts = LENGTH es.contexts)
           (stack_original_step o SND) (INL (), es)
End

Definition stack_original_run_create_def:
  stack_original_run_create dom static chainId prevHashes blk accounts tx =
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

Definition stack_original_run_transaction_def:
  stack_original_run_transaction dom static chainId prevHashes blk accounts tx =
  case stack_original_run_create dom static chainId prevHashes blk accounts tx of
     | SOME (INL result) => SOME result
     | SOME (INR (acc, s1, precomp)) => (case
          case precomp
            of NONE => stack_original_run s1
             | SOME addr => SOME $
                 handle (dispatch_precompiles addr) handle_step s1
       of
       | SOME (INR r, s2) => SOME $
          post_transaction_accounting blk tx r acc s2
       | _ => NONE)
     | _ => NONE
End

(* The bottom saved account map is no longer a rollback source. All other
   saved-frame data remain represented exactly, including root metadata. *)
Definition original_state_rel_def:
  original_state_rel old new ⇔
    old.contexts ≠ [] ∧ new.contexts ≠ [] ∧
    old.txParams = new.txParams ∧ old.rollback = new.rollback ∧
    old.msdomain = new.msdomain ∧
    FRONT old.contexts = FRONT new.contexts ∧
    FST (LAST old.contexts) = FST (LAST new.contexts) ∧
    SND (LAST old.contexts) =
      (SND (LAST new.contexts) with accounts := new.originalAccounts)
End

(* Private proof interface for the representation relation. *)
Definition orig_exec_rel_def:
  orig_exec_rel f g <=> !old new. original_state_rel old new ==>
    FST (f old) = FST (g new) /\
    original_state_rel (SND (f old)) (SND (g new))
End

Theorem original_state_rel_fields[local]:
  original_state_rel old new ==>
  old.contexts <> [] /\ new.contexts <> [] /\
  old.txParams = new.txParams /\ old.rollback = new.rollback /\
  old.msdomain = new.msdomain
Proof
  simp[original_state_rel_def]
QED

Theorem original_state_rel_length[local]:
  original_state_rel old new ==>
  LENGTH old.contexts = LENGTH new.contexts
Proof
  strip_tac >> fs[original_state_rel_def] >>
  `LENGTH (FRONT old.contexts) = LENGTH (FRONT new.contexts)` by simp[] >>
  fs[LENGTH_FRONT] >>
  Cases_on `old.contexts` >> Cases_on `new.contexts` >> gvs[]
QED

Theorem original_state_rel_current[local]:
  original_state_rel old new ==>
  FST (HD old.contexts) = FST (HD new.contexts)
Proof
  strip_tac >>
  drule original_state_rel_length >> strip_tac >>
  fs[original_state_rel_def] >>
  Cases_on `old.contexts` >> Cases_on `new.contexts` >> gvs[] >>
  Cases_on `t` >> Cases_on `t'` >> gvs[]
QED

Theorem original_state_get_original[local]:
  orig_exec_rel stack_original_get_original get_original
Proof
  rw[orig_exec_rel_def] >>
  fs[original_state_rel_def, stack_original_get_original_def,
     get_original_def, return_def]
QED

Theorem original_state_set_original[local]:
  orig_exec_rel (stack_original_set_original a) (set_original a)
Proof
  rw[orig_exec_rel_def] >>
  fs[original_state_rel_def, stack_original_set_original_def,
     set_original_def, return_def, set_last_accounts_def]
QED

Theorem original_state_rel_rollback[local]:
  original_state_rel old new ==>
  original_state_rel (old with rollback := r) (new with rollback := r)
Proof
  simp[original_state_rel_def]
QED

Theorem original_state_rel_push[local]:
  original_state_rel old new ==>
  original_state_rel (old with contexts updated_by CONS crb)
                     (new with contexts updated_by CONS crb)
Proof
  strip_tac >> fs[original_state_rel_def] >>
  Cases_on `old.contexts` >> Cases_on `new.contexts` >> gvs[]
QED

Theorem original_state_rel_set_current[local]:
  original_state_rel old new ==>
  original_state_rel
    (old with contexts := (c, SND (HD old.contexts))::TL old.contexts)
    (new with contexts := (c, SND (HD new.contexts))::TL new.contexts)
Proof
  strip_tac >> drule original_state_rel_length >> strip_tac >>
  fs[original_state_rel_def] >>
  Cases_on `old.contexts` >> Cases_on `new.contexts` >> gvs[] >>
  Cases_on `t` >> Cases_on `t'` >> gvs[]
QED

Theorem original_state_rel_pop[local]:
  original_state_rel old new /\ 1 < LENGTH old.contexts ==>
  HD old.contexts = HD new.contexts /\
  original_state_rel (old with contexts updated_by TL)
                     (new with contexts updated_by TL)
Proof
  strip_tac >> drule original_state_rel_length >> strip_tac >>
  fs[original_state_rel_def] >>
  Cases_on `old.contexts` >> Cases_on `new.contexts` >> gvs[] >>
  Cases_on `t` >> Cases_on `t'` >> gvs[]
QED

Theorem original_state_current[local]:
  orig_exec_rel get_current_context get_current_context
Proof
  rw[orig_exec_rel_def] >>
  drule original_state_rel_current >>
  drule original_state_rel_fields >>
  simp[get_current_context_def, return_def]
QED

Theorem original_state_set_current[local]:
  orig_exec_rel (set_current_context c) (set_current_context c)
Proof
  rw[orig_exec_rel_def] >>
  drule original_state_rel_fields >> strip_tac >>
  simp[set_current_context_def, return_def, original_state_rel_set_current]
QED

Theorem original_state_push[local]:
  orig_exec_rel (push_context crb) (push_context crb)
Proof
  simp[orig_exec_rel_def, push_context_def, return_def,
       original_state_rel_push]
QED

Theorem original_state_pop[local]:
  original_state_rel old new /\ 1 < LENGTH old.contexts ==>
  FST (pop_context old) = FST (pop_context new) /\
  original_state_rel (SND (pop_context old)) (SND (pop_context new))
Proof
  strip_tac >> drule_all original_state_rel_pop >>
  drule original_state_rel_fields >>
  simp[pop_context_def, return_def]
QED

(* Compositional rules include failure as well as successful results. *)
Theorem orig_exec_return[local]:
  orig_exec_rel (return x) (return x)
Proof
  simp[orig_exec_rel_def, return_def]
QED

Theorem orig_exec_fail[local]:
  orig_exec_rel (fail e) (fail e)
Proof
  simp[orig_exec_rel_def, fail_def]
QED

Theorem orig_exec_finish[local]:
  orig_exec_rel finish finish
Proof
  simp[orig_exec_rel_def, finish_def]
QED

Theorem orig_exec_revert[local]:
  orig_exec_rel revert revert
Proof
  simp[orig_exec_rel_def, revert_def]
QED

Theorem orig_exec_assert[local]:
  orig_exec_rel (assert b e) (assert b e)
Proof
  simp[orig_exec_rel_def, assert_def]
QED

Theorem orig_exec_reraise[local]:
  orig_exec_rel (reraise e) (reraise e)
Proof
  simp[orig_exec_rel_def, reraise_def]
QED

Theorem orig_exec_bind[local]:
  orig_exec_rel f g /\ (!x. orig_exec_rel (k x) (l x)) ==>
  orig_exec_rel (bind f k) (bind g l)
Proof
  rw[orig_exec_rel_def] >>
  qpat_x_assum `!s t. original_state_rel s t ==> FST (f s) = _ /\ _` drule >> strip_tac >>
  Cases_on `f old` >> Cases_on `g new` >> gvs[] >>
  Cases_on `q` >> gvs[bind_def]
QED

Theorem orig_exec_ignore_bind[local]:
  orig_exec_rel f g /\ orig_exec_rel k l ==>
  orig_exec_rel (ignore_bind f k) (ignore_bind g l)
Proof
  simp[ignore_bind_def, orig_exec_bind]
QED

Theorem orig_exec_handle[local]:
  orig_exec_rel f g /\ (!e. orig_exec_rel (h e) (k e)) ==>
  orig_exec_rel (handle f h) (handle g k)
Proof
  rw[orig_exec_rel_def] >>
  qpat_x_assum `!s t. original_state_rel s t ==> FST (f s) = _ /\ _` drule >> strip_tac >>
  Cases_on `f old` >> Cases_on `g new` >> gvs[] >>
  Cases_on `q` >> gvs[handle_def]
QED

Theorem orig_exec_rollback_read[local]:
  orig_exec_rel (\s. return (f s.rollback) s)
                (\s. return (f s.rollback) s)
Proof
  rw[orig_exec_rel_def, return_def] >>
  drule original_state_rel_fields >> simp[]
QED

Theorem orig_exec_rollback_update[local]:
  orig_exec_rel (\s. return () (s with rollback updated_by f))
                (\s. return () (s with rollback updated_by f))
Proof
  rw[orig_exec_rel_def, return_def] >>
  drule original_state_rel_fields >> strip_tac >>
  fs[original_state_rel_def]
QED

Theorem orig_exec_get_accounts[local]:
  orig_exec_rel get_accounts get_accounts
Proof
  rewrite_tac[lambdify get_accounts_def] >>
  irule orig_exec_rollback_read
QED

Theorem orig_exec_get_rollback[local]:
  orig_exec_rel get_rollback get_rollback
Proof
  rw[orig_exec_rel_def, get_rollback_def, return_def] >>
  drule original_state_rel_fields >> simp[]
QED

Theorem orig_exec_get_tStorage[local]:
  orig_exec_rel get_tStorage get_tStorage
Proof
  rewrite_tac[lambdify get_tStorage_def] >>
  irule orig_exec_rollback_read
QED

Theorem orig_exec_update_accounts[local]:
  orig_exec_rel (update_accounts f) (update_accounts f)
Proof
  rewrite_tac[lambdify update_accounts_def] >> BETA_TAC >>
  irule orig_exec_rollback_update
QED

Theorem orig_exec_set_tStorage[local]:
  orig_exec_rel (set_tStorage x) (set_tStorage x)
Proof
  rewrite_tac[lambdify set_tStorage_def] >> BETA_TAC >>
  irule orig_exec_rollback_update
QED

Theorem orig_exec_add_to_delete[local]:
  orig_exec_rel (add_to_delete a) (add_to_delete a)
Proof
  rewrite_tac[lambdify add_to_delete_def] >> BETA_TAC >>
  irule orig_exec_rollback_update
QED

Theorem orig_exec_set_rollback[local]:
  orig_exec_rel (set_rollback r) (set_rollback r)
Proof
  simp[orig_exec_rel_def, set_rollback_def, return_def,
       original_state_rel_rollback]
QED

Theorem orig_exec_get_num_contexts[local]:
  orig_exec_rel get_num_contexts get_num_contexts
Proof
  rw[orig_exec_rel_def, get_num_contexts_def, return_def] >>
  simp[original_state_rel_length]
QED

Theorem orig_exec_get_tx_params[local]:
  orig_exec_rel get_tx_params get_tx_params
Proof
  rw[orig_exec_rel_def, get_tx_params_def, return_def] >>
  drule original_state_rel_fields >> simp[]
QED

Theorem orig_exec_get_gas_left[local]:
  orig_exec_rel get_gas_left get_gas_left
Proof
  simp[get_gas_left_def, orig_exec_bind, original_state_current,
       orig_exec_return]
QED

Theorem orig_exec_context_reads[local]:
  !offset size.
  orig_exec_rel get_callee get_callee /\
  orig_exec_rel get_caller get_caller /\
  orig_exec_rel get_value get_value /\
  orig_exec_rel get_output_to get_output_to /\
  orig_exec_rel get_return_data get_return_data /\
  orig_exec_rel get_static get_static /\
  orig_exec_rel get_current_code get_current_code /\
  orig_exec_rel get_call_data get_call_data /\
  orig_exec_rel (memory_expansion_info offset size) (memory_expansion_info offset size) /\
  orig_exec_rel (read_memory offset size) (read_memory offset size)
Proof
  simp[get_callee_def, get_caller_def, get_value_def, get_output_to_def,
       get_return_data_def, get_static_def, get_current_code_def,
       get_call_data_def, memory_expansion_info_def, read_memory_def,
       orig_exec_bind, original_state_current, orig_exec_return]
QED

Theorem orig_exec_context_updates[local]:
  !rd jd ls add sub n v offset bytes.
  orig_exec_rel (set_return_data rd) (set_return_data rd) /\
  orig_exec_rel (set_jump_dest jd) (set_jump_dest jd) /\
  orig_exec_rel (push_logs ls) (push_logs ls) /\
  orig_exec_rel (update_gas_refund (add,sub)) (update_gas_refund (add,sub)) /\
  orig_exec_rel (consume_gas n) (consume_gas n) /\
  orig_exec_rel (unuse_gas n) (unuse_gas n) /\
  orig_exec_rel (pop_stack n) (pop_stack n) /\
  orig_exec_rel (push_stack v) (push_stack v) /\
  orig_exec_rel (expand_memory n) (expand_memory n) /\
  orig_exec_rel (write_memory offset bytes) (write_memory offset bytes)
Proof
  simp[set_return_data_def, set_jump_dest_def, push_logs_def,
       update_gas_refund_def, consume_gas_def, unuse_gas_def,
       pop_stack_def, push_stack_def, expand_memory_def, write_memory_def,
       orig_exec_bind, orig_exec_ignore_bind, original_state_current,
       original_state_set_current, orig_exec_return, orig_exec_assert]
QED

Theorem orig_exec_simple_wrappers[local]:
  !offset size a key value.
  orig_exec_rel (get_code a) (get_code a) /\
  orig_exec_rel (get_return_data_check offset size) (get_return_data_check offset size) /\
  orig_exec_rel (write_storage a key value) (write_storage a key value) /\
  orig_exec_rel (write_transient_storage a key value) (write_transient_storage a key value) /\
  orig_exec_rel assert_not_static assert_not_static
Proof
  simp[get_code_def, get_return_data_check_def, write_storage_def,
       write_transient_storage_def, assert_not_static_def,
       orig_exec_bind, orig_exec_ignore_bind, orig_exec_context_reads,
       orig_exec_get_accounts, orig_exec_get_tStorage, orig_exec_set_tStorage,
       orig_exec_update_accounts, orig_exec_assert, orig_exec_return]
QED

Theorem orig_exec_set_domain[local]:
  orig_exec_rel (set_domain d) (set_domain d)
Proof
  simp[orig_exec_rel_def, set_domain_def, return_def,
       original_state_rel_def]
QED

Theorem orig_exec_domain_check[local]:
  !f g err check add.
  orig_exec_rel f g ==>
  orig_exec_rel (domain_check err check add f) (domain_check err check add g)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[orig_exec_rel_def] >> rpt gen_tac >> strip_tac >>
  `old.msdomain = new.msdomain` by metis_tac[original_state_rel_fields] >>
  Cases_on `new.msdomain`
  >- (Cases_on `check d` >>
      gvs[domain_check_def, fail_def] >>
      fs[orig_exec_rel_def]) >>
  gvs[domain_check_def, ignore_bind_def, bind_def, set_domain_def, return_def] >>
  fs[orig_exec_rel_def] >> first_x_assum irule >>
  fs[original_state_rel_def]
QED

Theorem orig_exec_access_address[local]:
  orig_exec_rel (access_address a) (access_address a)
Proof
  rewrite_tac[access_address_def] >> irule orig_exec_domain_check >>
  rw[orig_exec_rel_def, return_def] >>
  drule original_state_rel_fields >> strip_tac >>
  fs[original_state_rel_def]
QED

Theorem orig_exec_access_slot[local]:
  orig_exec_rel (access_slot x) (access_slot x)
Proof
  rewrite_tac[access_slot_def] >> irule orig_exec_domain_check >>
  rw[orig_exec_rel_def, return_def] >>
  drule original_state_rel_fields >> strip_tac >>
  fs[original_state_rel_def]
QED

Theorem orig_exec_ensure_storage[local]:
  orig_exec_rel (ensure_storage_in_domain a) (ensure_storage_in_domain a)
Proof
  simp[ensure_storage_in_domain_def, orig_exec_domain_check, orig_exec_return]
QED

Theorem orig_exec_copy_to_memory[local]:
  !gas offset sourceOffset size getSource.
  (!f. getSource = SOME f ==> orig_exec_rel f f) ==>
  orig_exec_rel (copy_to_memory gas offset sourceOffset size getSource)
                (copy_to_memory gas offset sourceOffset size getSource)
Proof
  map_every qx_gen_tac [`gas`, `offset`, `sourceOffset`, `sz`, `getSource`] >>
  strip_tac >>
  Cases_on `max_expansion_range (offset,sz) (sourceOffset,sz)` >>
  Cases_on `getSource` >>
  fs[copy_to_memory_def, orig_exec_bind, orig_exec_ignore_bind,
     orig_exec_context_reads, orig_exec_context_updates, orig_exec_return] >>
  irule orig_exec_bind >> simp[orig_exec_context_reads] >>
  gen_tac >> irule orig_exec_ignore_bind >> simp[orig_exec_context_updates] >>
  irule orig_exec_bind >> simp[orig_exec_context_updates] >>
  irule orig_exec_bind >> simp[orig_exec_ignore_bind,
       orig_exec_context_updates, orig_exec_return]
QED

Theorem orig_exec_cond[local]:
  orig_exec_rel f g /\ orig_exec_rel h k ==>
  orig_exec_rel (if b then f else h) (if b then g else k)
Proof
  Cases_on `b` >> simp[]
QED

Theorem orig_exec_refund[local]:
  orig_exec_rel (update_gas_refund refunds) (update_gas_refund refunds)
Proof
  Cases_on `refunds` >> simp[orig_exec_context_updates]
QED

Theorem orig_exec_sstore_gas[local]:
  orig_exec_rel (stack_original_step_sstore_gas_consumption address key value)
                (step_sstore_gas_consumption address key value)
Proof
  rewrite_tac[stack_original_step_sstore_gas_consumption_def,
              step_sstore_gas_consumption_def] >>
  irule orig_exec_bind >> simp[orig_exec_get_gas_left] >> gen_tac >>
  irule orig_exec_ignore_bind >> simp[orig_exec_assert] >>
  irule orig_exec_bind >> simp[orig_exec_get_accounts] >> gen_tac >>
  simp[sstore_base_gas_def,
       sstore_refund_updates_def, orig_exec_bind, orig_exec_ignore_bind,
       orig_exec_get_gas_left, orig_exec_get_accounts,
       original_state_get_original, orig_exec_access_slot,
       orig_exec_refund, orig_exec_context_updates, orig_exec_assert]
QED

Theorem orig_exec_sstore[local]:
  orig_exec_rel (stack_original_step_sstore transient) (step_sstore transient)
Proof
  Cases_on `transient` >>
  simp[stack_original_step_sstore_def, step_sstore_def,
       orig_exec_bind, orig_exec_ignore_bind, orig_exec_sstore_gas,
       orig_exec_context_reads, orig_exec_context_updates,
       orig_exec_simple_wrappers]
QED

Theorem orig_exec_self_destruct[local]:
  orig_exec_rel stack_original_step_self_destruct step_self_destruct
Proof
  rewrite_tac[stack_original_step_self_destruct_def, step_self_destruct_def,
              ignore_bind_def] >>
  rpt (irule orig_exec_bind >>
       simp[orig_exec_bind, orig_exec_cond,
            orig_exec_context_reads, orig_exec_context_updates,
            orig_exec_get_accounts, orig_exec_update_accounts,
            original_state_get_original, orig_exec_access_address,
            orig_exec_simple_wrappers, orig_exec_return,
            orig_exec_add_to_delete, orig_exec_finish] >> rpt gen_tac)
QED

Theorem orig_exec_proceed_create[local]:
  orig_exec_rel (stack_original_proceed_create senderAddress address value code cappedGas)
                (proceed_create senderAddress address value code cappedGas)
Proof
  rewrite_tac[stack_original_proceed_create_def, proceed_create_def, ignore_bind_def] >>
  rpt (irule orig_exec_bind >>
       simp[orig_exec_bind, orig_exec_update_accounts,
            orig_exec_get_rollback, original_state_get_original,
            original_state_set_original, original_state_push] >> rpt gen_tac)
QED

Theorem orig_exec_create_aborts[local]:
  orig_exec_rel inc_pc inc_pc /\
  orig_exec_rel (abort_unuse n) (abort_unuse n) /\
  orig_exec_rel (abort_create_exists a) (abort_create_exists a) /\
  orig_exec_rel (abort_call_value n) (abort_call_value n)
Proof
  simp[inc_pc_def, abort_unuse_def, abort_create_exists_def, abort_call_value_def,
       orig_exec_bind, orig_exec_ignore_bind, orig_exec_update_accounts,
       original_state_current, original_state_set_current,
       orig_exec_context_updates]
QED

Theorem orig_exec_create[local]:
  orig_exec_rel (stack_original_step_create two) (step_create two)
Proof
  rewrite_tac[stack_original_step_create_def, step_create_def, ignore_bind_def] >>
  rpt (irule orig_exec_bind >>
       simp[orig_exec_bind, orig_exec_cond,
            orig_exec_context_reads, orig_exec_context_updates,
            orig_exec_get_accounts, orig_exec_get_gas_left, orig_exec_get_num_contexts,
            orig_exec_assert, orig_exec_simple_wrappers, orig_exec_access_address,
            orig_exec_ensure_storage, orig_exec_create_aborts, orig_exec_proceed_create] >>
       rpt gen_tac)
QED

(* Unchanged instructions use only the compatible primitive interface. *)
Theorem orig_exec_shared_arithmetic[local]:
  orig_exec_rel (step_binop op f) (step_binop op f) /\
  orig_exec_rel (step_monop op g) (step_monop op g) /\
  orig_exec_rel (step_modop op h) (step_modop op h) /\
  orig_exec_rel (step_context op k) (step_context op k) /\
  orig_exec_rel (step_msgParams op m) (step_msgParams op m) /\
  orig_exec_rel (step_txParams op t) (step_txParams op t) /\
  orig_exec_rel step_exp step_exp
Proof
  simp[step_binop_def, step_monop_def, step_modop_def, step_context_def,
       step_msgParams_def, step_txParams_def, step_exp_def,
       orig_exec_bind, orig_exec_ignore_bind, orig_exec_return,
       original_state_current, orig_exec_context_updates, orig_exec_get_tx_params]
QED

Theorem orig_exec_shared_data[local]:
  orig_exec_rel step_keccak256 step_keccak256 /\
  orig_exec_rel (step_sload transient) (step_sload transient) /\
  orig_exec_rel step_balance step_balance /\
  orig_exec_rel step_call_data_load step_call_data_load /\
  orig_exec_rel step_ext_code_size step_ext_code_size /\
  orig_exec_rel step_ext_code_hash step_ext_code_hash /\
  orig_exec_rel step_block_hash step_block_hash /\
  orig_exec_rel step_blob_hash step_blob_hash /\
  orig_exec_rel step_self_balance step_self_balance /\
  orig_exec_rel step_mload step_mload /\
  orig_exec_rel (step_mstore op) (step_mstore op) /\
  orig_exec_rel step_jump step_jump /\
  orig_exec_rel step_jumpi step_jumpi /\
  orig_exec_rel (step_push n ws) (step_push n ws) /\
  orig_exec_rel step_pop step_pop /\
  orig_exec_rel (step_dup n) (step_dup n) /\
  orig_exec_rel (step_swap n) (step_swap n) /\
  orig_exec_rel step_dupn step_dupn /\
  orig_exec_rel step_swapn step_swapn /\
  orig_exec_rel step_exchange step_exchange /\
  orig_exec_rel (step_log n) (step_log n) /\
  orig_exec_rel (step_return b) (step_return b)
Proof
  rpt conj_tac >>
  rewrite_tac[step_keccak256_def, step_sload_def, step_balance_def,
    step_call_data_load_def, step_ext_code_size_def, step_ext_code_hash_def,
    step_block_hash_def, step_blob_hash_def, step_self_balance_def,
    step_mload_def, step_mstore_def, step_jump_def, step_jumpi_def,
    step_push_def, step_pop_def, step_dup_def, step_swap_def,
    step_dupn_def, step_swapn_def, step_exchange_def, code_byte_def,
    exchange_stack_def,
    step_log_def, step_return_def, ignore_bind_def] >>
  rpt (irule orig_exec_bind >>
       simp[orig_exec_bind, orig_exec_cond, orig_exec_return,
            orig_exec_assert, orig_exec_finish, orig_exec_revert,
            original_state_current, original_state_set_current,
            orig_exec_context_reads, orig_exec_context_updates,
            orig_exec_simple_wrappers, orig_exec_get_accounts,
            orig_exec_get_tStorage, orig_exec_get_tx_params,
            orig_exec_access_address, orig_exec_access_slot] >> rpt gen_tac)
QED

Theorem orig_exec_shared_copy[local]:
  (!f. getSource = SOME f ==> orig_exec_rel f f) ==>
  orig_exec_rel (step_copy_to_memory op getSource) (step_copy_to_memory op getSource)
Proof
  strip_tac >> rewrite_tac[step_copy_to_memory_def] >>
  irule orig_exec_bind >> simp[orig_exec_context_updates, orig_exec_copy_to_memory]
QED

Theorem orig_exec_shared_code_copy[local]:
  orig_exec_rel step_return_data_copy step_return_data_copy /\
  orig_exec_rel step_ext_code_copy step_ext_code_copy
Proof
  simp[step_return_data_copy_def, step_ext_code_copy_def,
       orig_exec_bind, orig_exec_context_updates, orig_exec_access_address,
       orig_exec_copy_to_memory, orig_exec_simple_wrappers]
QED

Theorem orig_exec_option[local]:
  orig_exec_rel n m /\ (!x. orig_exec_rel (f x) (g x)) ==>
  orig_exec_rel (case opt of NONE => n | SOME x => f x)
                (case opt of NONE => m | SOME x => g x)
Proof
  Cases_on `opt` >> simp[]
QED

Theorem orig_exec_pair[local]:
  (!x y. orig_exec_rel (f x y) (g x y)) ==>
  orig_exec_rel (case p of (x,y) => f x y) (case p of (x,y) => g x y)
Proof
  Cases_on `p` >> simp[]
QED

Theorem orig_exec_precompiles[local]:
  orig_exec_rel precompile_ecrecover precompile_ecrecover /\
  orig_exec_rel precompile_identity precompile_identity /\
  orig_exec_rel precompile_modexp precompile_modexp /\
  orig_exec_rel precompile_sha2_256 precompile_sha2_256 /\
  orig_exec_rel precompile_ripemd_160 precompile_ripemd_160 /\
  orig_exec_rel precompile_ecadd precompile_ecadd /\
  orig_exec_rel precompile_ecmul precompile_ecmul /\
  orig_exec_rel precompile_ecpairing precompile_ecpairing /\
  orig_exec_rel precompile_blake2f precompile_blake2f /\
  orig_exec_rel precompile_point_eval precompile_point_eval /\
  orig_exec_rel precompile_bls_g1add precompile_bls_g1add /\
  orig_exec_rel precompile_bls_g1msm precompile_bls_g1msm /\
  orig_exec_rel precompile_bls_g2add precompile_bls_g2add /\
  orig_exec_rel precompile_bls_g2msm precompile_bls_g2msm /\
  orig_exec_rel precompile_bls_pairing precompile_bls_pairing /\
  orig_exec_rel precompile_bls_map_fp_to_g1 precompile_bls_map_fp_to_g1 /\
  orig_exec_rel precompile_bls_map_fp2_to_g2 precompile_bls_map_fp2_to_g2 /\
  orig_exec_rel precompile_p256verify precompile_p256verify
Proof
  rpt conj_tac >>
  rewrite_tac[precompile_ecrecover_def, precompile_identity_def,
    precompile_modexp_def, precompile_sha2_256_def, precompile_ripemd_160_def,
    precompile_ecadd_def, precompile_ecmul_def, precompile_ecpairing_def,
    precompile_blake2f_def, precompile_point_eval_def, precompile_bls_g1add_def,
    precompile_bls_g1msm_def, precompile_bls_g2add_def, precompile_bls_g2msm_def,
    precompile_bls_pairing_def, precompile_bls_map_fp_to_g1_def,
    precompile_bls_map_fp2_to_g2_def, precompile_p256verify_def, ignore_bind_def] >>
  rpt (irule orig_exec_bind >>
       simp[orig_exec_bind, orig_exec_cond, orig_exec_option, orig_exec_pair,
            orig_exec_return, orig_exec_assert, orig_exec_fail, orig_exec_finish,
            orig_exec_context_reads, orig_exec_context_updates] >> rpt gen_tac) >>
  irule orig_exec_cond >> simp[orig_exec_fail] >>
  rpt (irule orig_exec_bind >>
       simp[orig_exec_bind, orig_exec_option, orig_exec_return,
            orig_exec_assert, orig_exec_fail, orig_exec_finish,
            orig_exec_context_updates] >> rpt gen_tac)
QED

Theorem orig_exec_dispatch_precompiles[local]:
  orig_exec_rel (dispatch_precompiles a) (dispatch_precompiles a)
Proof
  rewrite_tac[dispatch_precompiles_def] >>
  rpt (irule orig_exec_cond >> simp[orig_exec_precompiles, orig_exec_fail])
QED

Theorem orig_exec_proceed_call[local]:
  orig_exec_rel
    (proceed_call op sender address value argsOffset argsSize code stipend outputTo)
    (proceed_call op sender address value argsOffset argsSize code stipend outputTo)
Proof
  rewrite_tac[proceed_call_def, ignore_bind_def] >>
  rpt (irule orig_exec_bind >>
       simp[orig_exec_bind, orig_exec_cond, orig_exec_return,
            orig_exec_get_rollback, orig_exec_update_accounts, original_state_push,
            orig_exec_context_reads, orig_exec_dispatch_precompiles] >> rpt gen_tac)
QED

Theorem orig_exec_call[local]:
  orig_exec_rel (step_call op) (step_call op)
Proof
  simp_tac bool_ss [step_call_def, LET_THM] >>
  irule orig_exec_bind >> simp[orig_exec_context_updates] >>
  qx_gen_tac `args` >> pairarg_tac >> gvs[] >>
  rewrite_tac[ignore_bind_def] >>
  rpt (irule orig_exec_bind >>
       simp[orig_exec_bind, orig_exec_cond, orig_exec_option, orig_exec_pair,
            FORALL_PROD, orig_exec_return, orig_exec_assert,
            orig_exec_context_reads, orig_exec_context_updates,
            orig_exec_get_accounts, orig_exec_get_gas_left,
            orig_exec_get_num_contexts, orig_exec_access_address,
            orig_exec_simple_wrappers, orig_exec_create_aborts,
            orig_exec_proceed_call] >> rpt gen_tac) >>
  pairarg_tac >> gvs[] >>
  rpt (irule orig_exec_bind >>
       simp[orig_exec_bind, orig_exec_cond, orig_exec_return,
            orig_exec_context_reads, orig_exec_context_updates,
            orig_exec_get_num_contexts, orig_exec_simple_wrappers,
            orig_exec_create_aborts, orig_exec_proceed_call] >> rpt gen_tac)
QED

Theorem orig_exec_inc_pc_or_jump[local]:
  orig_exec_rel (inc_pc_or_jump op) (inc_pc_or_jump op)
Proof
  simp[inc_pc_or_jump_def, orig_exec_cond, orig_exec_return, orig_exec_bind,
       orig_exec_option, orig_exec_ignore_bind, orig_exec_assert,
       original_state_current, original_state_set_current]
QED

Theorem orig_exec_tstore[local]:
  orig_exec_rel (step_sstore T) (step_sstore T)
Proof
  simp[step_sstore_def, orig_exec_bind, orig_exec_ignore_bind,
       orig_exec_context_reads, orig_exec_context_updates, orig_exec_simple_wrappers]
QED

Theorem orig_exec_inst[local]:
  orig_exec_rel (stack_original_step_inst op) (step_inst op)
Proof
  Cases_on `op` >>
  simp[stack_original_step_inst_def, step_inst_def,
       orig_exec_sstore, orig_exec_self_destruct, orig_exec_create,
       orig_exec_shared_arithmetic, orig_exec_shared_data,
       orig_exec_shared_copy, orig_exec_shared_code_copy,
       orig_exec_context_reads, orig_exec_context_updates,
       orig_exec_bind, orig_exec_ignore_bind,
       orig_exec_fail, orig_exec_finish, orig_exec_call, orig_exec_tstore]
QED

(* Settlement only removes a frame above the root. *)
Theorem orig_exec_handle_create[local]:
  orig_exec_rel (handle_create e) (handle_create e)
Proof
  rewrite_tac[handle_create_def] >>
  irule orig_exec_bind >> reverse conj_tac >- simp[orig_exec_context_reads] >>
  qx_gen_tac `code` >> BETA_TAC >>
  irule orig_exec_bind >> reverse conj_tac >- simp[orig_exec_context_reads] >>
  qx_gen_tac `dest` >>
  Cases_on `e` >> Cases_on `dest` >>
  simp[ignore_bind_def, orig_exec_bind, orig_exec_reraise,
       orig_exec_assert, orig_exec_context_updates, orig_exec_update_accounts]
QED

Theorem original_state_bind_at[local]:
  FST (f old) = FST (g new) /\
  original_state_rel (SND (f old)) (SND (g new)) /\
  (!x. orig_exec_rel (k x) (l x)) ==>
  FST (bind f k old) = FST (bind g l new) /\
  original_state_rel (SND (bind f k old)) (SND (bind g l new))
Proof
  strip_tac >> Cases_on `f old` >> Cases_on `g new` >> gvs[] >>
  Cases_on `q` >> gvs[bind_def] >> metis_tac[orig_exec_rel_def]
QED

Theorem original_state_pop_bind[local]:
  (!x. orig_exec_rel (k x) (l x)) /\
  original_state_rel old new /\ 1 < LENGTH old.contexts ==>
  FST (bind pop_context k old) = FST (bind pop_context l new) /\
  original_state_rel (SND (bind pop_context k old))
                     (SND (bind pop_context l new))
Proof
  strip_tac >> irule original_state_bind_at >>
  simp[original_state_pop]
QED

Theorem original_state_pop_incorporate[local]:
  original_state_rel old new /\ 1 < LENGTH old.contexts ==>
  FST (pop_and_incorporate_context success old) =
    FST (pop_and_incorporate_context success new) /\
  original_state_rel (SND (pop_and_incorporate_context success old))
                     (SND (pop_and_incorporate_context success new))
Proof
  strip_tac >> drule original_state_rel_current >> strip_tac >>
  drule original_state_rel_fields >> strip_tac >>
  `get_gas_left old =
     (INL ((FST (HD new.contexts)).msgParams.gasLimit -
           (FST (HD new.contexts)).gasUsed), old)` by
    simp[get_gas_left_def, get_current_context_def, bind_def, return_def] >>
  `get_gas_left new =
     (INL ((FST (HD new.contexts)).msgParams.gasLimit -
           (FST (HD new.contexts)).gasUsed), new)` by
    simp[get_gas_left_def, get_current_context_def, bind_def, return_def] >>
  rewrite_tac[pop_and_incorporate_context_def] >>
  once_rewrite_tac[bind_def] >> simp[] >>
  irule original_state_pop_bind >>
  simp[ignore_bind_def, orig_exec_bind, orig_exec_context_updates,
       orig_exec_cond, orig_exec_set_rollback]
QED

Theorem orig_exec_exception_output[local]:
  orig_exec_rel
    (do inc_pc;
        case dest of
        | Code address => if success then do set_return_data []; push_stack (w2w address) od
                          else do set_return_data output; push_stack (b2w F) od
        | Memory r => do set_return_data output; push_stack (b2w success);
                         write_memory r.offset (TAKE r.size output) od
     od)
    (do inc_pc;
        case dest of
        | Code address => if success then do set_return_data []; push_stack (w2w address) od
                          else do set_return_data output; push_stack (b2w F) od
        | Memory r => do set_return_data output; push_stack (b2w success);
                         write_memory r.offset (TAKE r.size output) od
     od)
Proof
  Cases_on `dest` >>
  simp[ignore_bind_def, orig_exec_bind, orig_exec_context_updates,
       orig_exec_cond, orig_exec_inc_pc_or_jump, inc_pc_def,
       original_state_current, original_state_set_current, orig_exec_return]
QED

Theorem orig_exec_handle_exception[local]:
  orig_exec_rel (handle_exception e) (handle_exception e)
Proof
  simp[handle_exception_def, ignore_bind_def] >>
  irule orig_exec_bind >> reverse conj_tac
  >- simp[orig_exec_cond, orig_exec_bind, orig_exec_get_gas_left,
          orig_exec_context_updates, orig_exec_return] >>
  simp[] >>
  rewrite_tac[orig_exec_rel_def] >> rpt gen_tac >> strip_tac >>
  drule original_state_rel_fields >> strip_tac >>
  drule original_state_rel_length >> strip_tac >>
  drule original_state_rel_current >> strip_tac >>
  once_rewrite_tac[bind_def] >> simp[get_num_contexts_def, return_def] >>
  Cases_on `LENGTH new.contexts <= 1`
  >- metis_tac[orig_exec_reraise, orig_exec_rel_def] >>
  `get_return_data old = (INL (FST (HD new.contexts)).returnData, old) /\
   get_return_data new = (INL (FST (HD new.contexts)).returnData, new) /\
   get_output_to old = (INL (FST (HD new.contexts)).msgParams.outputTo, old) /\
   get_output_to new = (INL (FST (HD new.contexts)).msgParams.outputTo, new)` by
    simp[get_return_data_def, get_output_to_def, get_current_context_def,
         bind_def, return_def] >>
  simp[] >> once_rewrite_tac[bind_def] >> simp[] >>
  once_rewrite_tac[bind_def] >> simp[] >>
  irule original_state_bind_at >>
  simp[original_state_pop_incorporate, GSYM ignore_bind_def,
       SRULE [] orig_exec_exception_output]
QED

Theorem orig_exec_handle_step[local]:
  orig_exec_rel (handle_step e) (handle_step e)
Proof
  simp[handle_step_def, orig_exec_cond, orig_exec_reraise,
       orig_exec_handle, orig_exec_handle_create, orig_exec_handle_exception]
QED

Theorem orig_exec_step[local]:
  orig_exec_rel stack_original_step step
Proof
  simp[stack_original_step_def, step_def] >>
  irule orig_exec_handle >> simp[orig_exec_handle_step] >>
  irule orig_exec_bind >> simp[original_state_current] >>
  gen_tac >>
  simp[orig_exec_option, orig_exec_cond, orig_exec_inst,
       orig_exec_ignore_bind, orig_exec_inc_pc_or_jump]
QED

Theorem original_state_step:
  original_state_rel old new ⇒
  FST (stack_original_step old) = FST (step new) ∧
  original_state_rel (SND (stack_original_step old)) (SND (step new))
Proof
  metis_tac[orig_exec_step, orig_exec_rel_def]
QED

(* Partial loops synchronize termination as well as their terminal values. *)
Theorem original_owhile_some[local]:
  (!x y. R x y ==> (P x = Q y)) /\
  (!x y. R x y /\ P x ==> R (f x) (g y)) ==>
  !x z. OWHILE P f x = SOME z ==>
  !y. R x y ==> ?w. OWHILE Q g y = SOME w /\ R z w
Proof
  strip_tac >> ho_match_mp_tac OWHILE_IND >> conj_tac
  >- (rpt strip_tac >> qexists_tac `y` >>
      simp[Once OWHILE_THM] >> metis_tac[]) >>
  rpt strip_tac >>
  `Q y /\ R (f x) (g y)` by metis_tac[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexists_tac `w` >> simp[Once OWHILE_THM]
QED

Theorem original_owhile_rel[local]:
  (!x y. R x y ==> (P x = Q y)) /\
  (!x y. R x y /\ P x ==> R (f x) (g y)) /\ R x y ==>
  OPTREL R (OWHILE P f x) (OWHILE Q g y)
Proof
  strip_tac >>
  `!y w. OWHILE Q g y = SOME w ==>
     !x. R x y ==> ?z. OWHILE P f x = SOME z /\ R z w` by
    (ho_match_mp_tac original_owhile_some >> metis_tac[]) >>
  `!x z. OWHILE P f x = SOME z ==>
     !y. R x y ==> ?w. OWHILE Q g y = SOME w /\ R z w` by
    (ho_match_mp_tac original_owhile_some >> simp[]) >>
  qpat_x_assum `!x y. R x y ==> _` kall_tac >>
  qpat_x_assum `!x y. R x y /\ P x ==> _` kall_tac >>
  Cases_on `OWHILE P f x`
  >- (Cases_on `OWHILE Q g y` >- simp[] >>
      qpat_x_assum `!y w. _` drule >>
      disch_then drule >> simp[]) >>
  qpat_x_assum `!x z. _` drule >>
  disch_then drule >> strip_tac >> gvs[]
QED

Theorem original_state_run:
  original_state_rel old new ⇒
  OPTREL (λ(r, s) (r', s'). r = r' ∧ original_state_rel s s')
    (stack_original_run old) (run new)
Proof
  strip_tac >> rewrite_tac[stack_original_run_def, run_def] >>
  irule original_owhile_rel >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >> simp[]) >>
  rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
  simp[UNCURRY] >> metis_tac[original_state_step]
QED

Theorem original_state_run_call:
  original_state_rel old new ⇒
  OPTREL (λ(r, s) (r', s'). r = r' ∧ original_state_rel s s')
    (stack_original_run_call old) (run_call new)
Proof
  strip_tac >> drule original_state_rel_length >> strip_tac >>
  rewrite_tac[stack_original_run_call_def, run_call_def] >>
  irule original_owhile_rel >> simp[] >> conj_tac
  >- (rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
      simp[] >> metis_tac[original_state_rel_length]) >>
  rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
  simp[UNCURRY] >> metis_tac[original_state_step]
QED

Theorem original_state_run_within_frame:
  original_state_rel old new ⇒
  OPTREL (λ(r, s) (r', s'). r = r' ∧ original_state_rel s s')
    (stack_original_run_within_frame old) (run_within_frame new)
Proof
  strip_tac >> drule original_state_rel_length >> strip_tac >>
  rewrite_tac[stack_original_run_within_frame_def, run_within_frame_def] >>
  irule original_owhile_rel >> simp[] >> conj_tac
  >- (rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
      simp[] >> metis_tac[original_state_rel_length]) >>
  rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
  simp[UNCURRY] >> metis_tac[original_state_step]
QED

(* Initialization and settlement observations. *)
Theorem original_state_initial[local]:
  initial_state dom static chainId prevHashes blk accounts tx = SOME s ==>
  LENGTH s.contexts = 1 /\ original_state_rel s s
Proof
  simp[initial_state_def] >>
  Cases_on `pre_transaction_updates accounts
    (base_fee_per_blob_gas blk.excessBlobGas) tx` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  gvs[original_state_rel_def, initial_rollback_def]
QED

Theorem original_state_accounting[local]:
  original_state_rel old new ==>
  post_transaction_accounting blk tx r acc old =
  post_transaction_accounting blk tx r acc new
Proof
  strip_tac >> drule original_state_rel_fields >> strip_tac >>
  drule original_state_rel_current >> strip_tac >>
  drule original_state_rel_length >> strip_tac >>
  `NULL old.contexts = NULL new.contexts /\
   NULL (TL old.contexts) = NULL (TL new.contexts)` by
    (Cases_on `old.contexts` >> Cases_on `new.contexts` >> gvs[] >>
     Cases_on `t` >> Cases_on `t'` >> gvs[]) >>
  simp[post_transaction_accounting_def]
QED

Theorem original_state_create[local]:
  OPTREL (\u v. case (u,v) of
      (INL r, INL r') => r = r'
    | (INR (acc,s,p), INR (acc',s',p')) =>
        acc = acc' /\ p = p' /\ original_state_rel s s'
    | _ => F)
    (stack_original_run_create dom static chainId prevHashes blk accounts tx)
    (run_create dom static chainId prevHashes blk accounts tx)
Proof
  rewrite_tac[stack_original_run_create_def, run_create_def] >>
  Cases_on `initial_state dom static chainId prevHashes blk accounts tx` >> simp[] >>
  drule original_state_initial >> strip_tac >>
  Cases_on `IS_SOME tx.to`
  >- gvs[original_state_rel_def] >>
  simp[] >> IF_CASES_TAC >> simp[] >>
  Cases_on `x.contexts` >> gvs[] >>
  PairCases_on `h` >> gvs[original_state_rel_def, set_last_accounts_def] >>
  fs[rollback_state_component_equality]
QED

Theorem original_state_transaction_execution[local]:
  original_state_rel old new ==>
  OPTREL (\(r,s) (r',s'). r = r' /\ original_state_rel s s')
    (case precomp of NONE => stack_original_run old
     | SOME a => SOME (handle (dispatch_precompiles a) handle_step old))
    (case precomp of NONE => run new
     | SOME a => SOME (handle (dispatch_precompiles a) handle_step new))
Proof
  strip_tac >> Cases_on `precomp` >> simp[original_state_run] >>
  `orig_exec_rel (handle (dispatch_precompiles x) handle_step)
                 (handle (dispatch_precompiles x) handle_step)` by
    simp[orig_exec_handle, orig_exec_dispatch_precompiles, orig_exec_handle_step] >>
  gvs[orig_exec_rel_def, UNCURRY]
QED

Theorem original_state_accounting_result[local]:
  OPTREL (\(r,s) (r',s'). r = r' /\ original_state_rel s s') a b ==>
  (case a of SOME (INR r,s) => SOME (post_transaction_accounting blk tx r acc s)
           | _ => NONE) =
  (case b of SOME (INR r,s) => SOME (post_transaction_accounting blk tx r acc s)
           | _ => NONE)
Proof
  Cases_on `a` >> Cases_on `b` >> simp[] >>
  PairCases_on `x` >> PairCases_on `x'` >> simp[] >>
  strip_tac >> gvs[] >> Cases_on `x'0` >>
  simp[original_state_accounting]
QED

Theorem original_state_run_transaction:
  stack_original_run_transaction dom static chainId prevHashes blk accounts tx =
  run_transaction dom static chainId prevHashes blk accounts tx
Proof
  mp_tac original_state_create >>
  rewrite_tac[stack_original_run_transaction_def, run_transaction_def] >>
  Cases_on `stack_original_run_create dom static chainId prevHashes blk accounts tx` >>
  Cases_on `run_create dom static chainId prevHashes blk accounts tx` >> simp[] >>
  Cases_on `x` >> Cases_on `x'` >> simp[] >>
  PairCases_on `y` >> PairCases_on `y'` >> simp[] >>
  strip_tac >> gvs[] >>
  irule original_state_accounting_result >>
  irule original_state_transaction_execution >> simp[]
QED

(* Fail the build if any exported correspondence acquires an oracle or axiom. *)
val _ = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if List.all (fn s => s = "DISK_THM") oracles andalso
       null axioms andalso null (Thm.hyp th)
    then () else raise Fail "original-state proof integrity audit"
  end)
  [original_state_step, original_state_run, original_state_run_call,
   original_state_run_within_frame, original_state_run_transaction];
