# Added lemmas: complete statement catalogue

Relative to `78466c68`, at source checkpoint `896b76f3`. Paths below are project-relative. HOL free variables are universally quantified as usual. Attributes are shown in headings. Proofs are in the cited source files, not duplicated here. ASCII `/\`, `==>`, `<>`, `<=`, `SUBSET` are the corresponding HOL notation. This catalogue excludes concurrent changes in the three explicitly excluded theories and prog. It includes local helpers and historical witnesses. Existing frozen restatements/replacements are covered by the TASK and the separate contract audit, not counted as new helpers.

## Eleven-primitive families

### spec/prop/vfmDomainCollectionScript.sml
```sml
Theorem state_gas_meter_computes_minimal_domain[simp]:
  computes_minimal_domain get_state_gas_left /\
  (!n. computes_minimal_domain (charge_state_gas n)) /\
  (!n. computes_minimal_domain (credit_state_gas_refund n)) /\
  computes_minimal_domain restore_state_gas /\
  computes_minimal_domain commit_state_gas /\
  (!sg. computes_minimal_domain (restore_state_gas_to_entry sg)) /\
  computes_minimal_domain repay_state_gas_spill /\
  computes_minimal_domain forfeit_remaining_gas /\
  computes_minimal_domain withhold_create_gas /\
  computes_minimal_domain drain_state_gas_reservoir /\
  (!gas reservoir. computes_minimal_domain (restore_child_gas gas reservoir))
```

### spec/prop/vfmDomainSeparationScript.sml
```sml
Theorem preserves_domain_has_callee_state_gas_meter[simp]:
  preserves_domain_has_callee (K T) get_state_gas_left /\
  preserves_domain_has_callee (K T) (charge_state_gas n) /\
  preserves_domain_has_callee (K T) (credit_state_gas_refund n) /\
  preserves_domain_has_callee (K T) restore_state_gas /\
  preserves_domain_has_callee (K T) commit_state_gas /\
  preserves_domain_has_callee (K T) (restore_state_gas_to_entry sg) /\
  preserves_domain_has_callee (K T) repay_state_gas_spill /\
  preserves_domain_has_callee (K T) forfeit_remaining_gas /\
  preserves_domain_has_callee (K T) withhold_create_gas /\
  preserves_domain_has_callee (K T) drain_state_gas_reservoir /\
  preserves_domain_has_callee (K T) (restore_child_gas gas reservoir)
```

### spec/prop/vfmHeadStackScript.sml
```sml
Theorem preserves_head_stack_state_gas_meter[simp]:
  preserves_head_stack get_state_gas_left /\
  preserves_head_stack (charge_state_gas n) /\
  preserves_head_stack (credit_state_gas_refund n) /\
  preserves_head_stack restore_state_gas /\
  preserves_head_stack commit_state_gas /\
  preserves_head_stack (restore_state_gas_to_entry sg) /\
  preserves_head_stack repay_state_gas_spill /\
  preserves_head_stack forfeit_remaining_gas /\
  preserves_head_stack withhold_create_gas /\
  preserves_head_stack drain_state_gas_reservoir /\
  preserves_head_stack (restore_child_gas gas reservoir)
```

### spec/prop/vfmJumpDestScript.sml
```sml
Theorem preserves_all_jumpDest_NONE_state_gas_meter[simp]:
  preserves_all_jumpDest_NONE get_state_gas_left /\
  (!n. preserves_all_jumpDest_NONE (charge_state_gas n)) /\
  (!n. preserves_all_jumpDest_NONE (credit_state_gas_refund n)) /\
  preserves_all_jumpDest_NONE restore_state_gas /\
  preserves_all_jumpDest_NONE commit_state_gas /\
  (!n. preserves_all_jumpDest_NONE (restore_state_gas_to_entry n)) /\
  preserves_all_jumpDest_NONE repay_state_gas_spill /\
  preserves_all_jumpDest_NONE forfeit_remaining_gas /\
  preserves_all_jumpDest_NONE withhold_create_gas /\
  preserves_all_jumpDest_NONE drain_state_gas_reservoir /\
  (!gas reservoir. preserves_all_jumpDest_NONE (restore_child_gas gas reservoir))

Theorem preserves_jumpDest_state_gas_meter[simp]:
  preserves_jumpDest get_state_gas_left /\
  (!n. preserves_jumpDest (charge_state_gas n)) /\
  (!n. preserves_jumpDest (credit_state_gas_refund n)) /\
  preserves_jumpDest restore_state_gas /\
  preserves_jumpDest commit_state_gas /\
  (!n. preserves_jumpDest (restore_state_gas_to_entry n)) /\
  preserves_jumpDest repay_state_gas_spill /\
  preserves_jumpDest forfeit_remaining_gas /\
  preserves_jumpDest withhold_create_gas /\
  preserves_jumpDest drain_state_gas_reservoir /\
  (!gas reservoir. preserves_jumpDest (restore_child_gas gas reservoir))
```

### spec/prop/vfmStoragePredicatesScript.sml
```sml
Theorem preserves_rollback_state_gas_meter[simp]:
  preserves_rollback get_state_gas_left /\
  preserves_rollback (charge_state_gas n) /\
  preserves_rollback (credit_state_gas_refund n) /\
  preserves_rollback restore_state_gas /\
  preserves_rollback commit_state_gas /\
  preserves_rollback (restore_state_gas_to_entry sg) /\
  preserves_rollback repay_state_gas_spill /\
  preserves_rollback forfeit_remaining_gas /\
  preserves_rollback withhold_create_gas /\
  preserves_rollback drain_state_gas_reservoir /\
  preserves_rollback (restore_child_gas gas reservoir)
```

### spec/prop/vfmStaticCallsScript.sml (pre-existing statement; proof completed)
```sml
Theorem cp_state_gas_meter[simp]:
  cp get_state_gas_left /\ cp (charge_state_gas n) /\
  cp (credit_state_gas_refund n) /\ cp restore_state_gas /\
  cp commit_state_gas /\ cp (restore_state_gas_to_entry sg) /\
  cp repay_state_gas_spill /\ cp forfeit_remaining_gas /\
  cp withhold_create_gas /\ cp drain_state_gas_reservoir /\
  cp (restore_child_gas g sr)
```

### spec/prop/vfmSameFrameScript.sml
```sml
Theorem preserves_same_frame_state_gas_meter[simp]:
  preserves_same_frame get_state_gas_left /\
  preserves_same_frame (charge_state_gas n) /\
  preserves_same_frame (credit_state_gas_refund n) /\
  (!s. s.contexts <> [] /\ (FST (HD s.contexts)).addRefund = 0 /\
       (FST (HD s.contexts)).subRefund = 0 ==>
       same_frame_rel s (SND (restore_state_gas s))) /\
  preserves_same_frame commit_state_gas /\
  preserves_same_frame (restore_state_gas_to_entry sg) /\
  preserves_same_frame repay_state_gas_spill /\
  preserves_same_frame forfeit_remaining_gas /\
  preserves_same_frame withhold_create_gas /\
  preserves_same_frame drain_state_gas_reservoir /\
  preserves_same_frame (restore_child_gas gas reservoir)
```

### spec/prop/vfmMsdomainPreservedScript.sml
```sml
Theorem SND_state_gas_meter_msdomain[simp]:
  (!s. (SND (get_state_gas_left s)).msdomain = s.msdomain) /\
  (!n s. (SND (charge_state_gas n s)).msdomain = s.msdomain) /\
  (!n s. (SND (credit_state_gas_refund n s)).msdomain = s.msdomain) /\
  (!s. (SND (restore_state_gas s)).msdomain = s.msdomain) /\
  (!s. (SND (commit_state_gas s)).msdomain = s.msdomain) /\
  (!sg s. (SND (restore_state_gas_to_entry sg s)).msdomain = s.msdomain) /\
  (!s. (SND (repay_state_gas_spill s)).msdomain = s.msdomain) /\
  (!s. (SND (forfeit_remaining_gas s)).msdomain = s.msdomain) /\
  (!s. (SND (withhold_create_gas s)).msdomain = s.msdomain) /\
  (!s. (SND (drain_state_gas_reservoir s)).msdomain = s.msdomain) /\
  (!gas reservoir s. (SND (restore_child_gas gas reservoir s)).msdomain = s.msdomain)
```

### spec/prop/vfmRunWithinFrameScript.sml
```sml
Theorem original_state_gas_meter[local,simp]:
  (!s. (SND (get_state_gas_left s)).originalAccounts = s.originalAccounts) /\
  (!n s. (SND (charge_state_gas n s)).originalAccounts = s.originalAccounts) /\
  (!n s. (SND (credit_state_gas_refund n s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (restore_state_gas s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (commit_state_gas s)).originalAccounts = s.originalAccounts) /\
  (!n s. (SND (restore_state_gas_to_entry n s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (repay_state_gas_spill s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (forfeit_remaining_gas s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (withhold_create_gas s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (drain_state_gas_reservoir s)).originalAccounts = s.originalAccounts) /\
  (!gas reservoir s. (SND (restore_child_gas gas reservoir s)).originalAccounts = s.originalAccounts)
```

## spec/prop/vfmStaticCallsScript.sml

```sml
Theorem cp_get_context_cond:
  cp (bind get_current_context f) /\ cp (bind get_current_context g) ==>
  cp (bind get_current_context (\c. if b c then f c else g c))

Theorem cp_get_set_context_then:
  (!c. (u c).msgParams = c.msgParams) /\
  (!c. (u c).logs = c.logs) /\ (!c. cp (k c)) ==>
  cp (bind get_current_context
       (\c. ignore_bind (set_current_context (u c)) (k c)))
```

## spec/prop/vfmDomainSeparationScript.sml

```sml
Theorem ignores_extra_domain_msdomain:
  !m s r t d. ignores_extra_domain m /\ m s = (r,t) /\
    s.msdomain = Enforce d ==> t.msdomain = s.msdomain

Theorem SND_drain_state_gas_reservoir_msdomain[simp]:
  (SND (drain_state_gas_reservoir s)).msdomain = s.msdomain
```

The `preserves_domain_has_callee_fail` and `preserves_domain_has_callee_unuse_gas` lemmas were relocated, not added.

## spec/prop/vfmSameFrameScript.sml

```sml
Theorem handle_exception_same_frame_counterexample:
  !s c rb.
    let s0 = s with contexts := [(c with addRefund := 1, rb)] in
    let out = handle_exception (SOME Reverted) s0 in
      s0.contexts <> [] /\
      LENGTH (SND out).contexts = LENGTH s0.contexts /\
      ~same_frame_rel s0 (SND out)

Theorem restore_state_gas_refund_counterexample:
  !s c rb.
    ~same_frame_rel (s with contexts := [(c with addRefund := 1, rb)])
      (SND (restore_state_gas
        (s with contexts := [(c with addRefund := 1, rb)])))

Theorem restore_state_gas_same_frame_iff:
  s.contexts <> [] ==>
  (same_frame_rel s (SND (restore_state_gas s)) <=>
   (FST (HD s.contexts)).addRefund = 0 /\
   (FST (HD s.contexts)).subRefund = 0)

Theorem zero_head_refunds_projections:
  s.contexts <> [] ==>
  LENGTH (zero_head_refunds s).contexts = LENGTH s.contexts /\
  TL (zero_head_refunds s).contexts = TL s.contexts /\
  SND (HD (zero_head_refunds s).contexts) = SND (HD s.contexts) /\
  (FST (HD (zero_head_refunds s).contexts)).msgParams =
    (FST (HD s.contexts)).msgParams /\
  (FST (HD (zero_head_refunds s).contexts)).logs =
    (FST (HD s.contexts)).logs /\
  (FST (HD (zero_head_refunds s).contexts)).gasUsed =
    (FST (HD s.contexts)).gasUsed /\
  (zero_head_refunds s).rollback = s.rollback /\
  (zero_head_refunds s).txParams = s.txParams /\
  (zero_head_refunds s).originalAccounts = s.originalAccounts /\
  (zero_head_refunds s).msdomain = s.msdomain

Theorem zero_head_refunds_idempotent:
  zero_head_refunds (zero_head_refunds s) = zero_head_refunds s

Theorem same_frame_rel_zero_head_refunds_refl:
  s.contexts <> [] ==> same_frame_rel (zero_head_refunds s) s

Theorem same_frame_rel_zero_head_refunds_weaken:
  same_frame_rel s t ==> same_frame_rel (zero_head_refunds s) t

Theorem same_frame_rel_zero_head_refunds_target:
  s.contexts <> [] /\ same_frame_rel (zero_head_refunds s) t ==>
  same_frame_rel (zero_head_refunds s) (zero_head_refunds t)

Theorem same_frame_rel_zero_head_refunds_trans:
  s.contexts <> [] /\ same_frame_rel (zero_head_refunds s) t /\
  same_frame_rel (zero_head_refunds t) u ==>
  same_frame_rel (zero_head_refunds s) u

Theorem outputTo_consistent_zero_head_refunds:
  s.contexts <> [] ==>
  (outputTo_consistent (zero_head_refunds s) <=> outputTo_consistent s)

Theorem same_frame_rel_zero_head_refunds_outputTo_consistent:
  s.contexts <> [] /\ outputTo_consistent s /\
  same_frame_rel (zero_head_refunds s) t ==> outputTo_consistent t
```

New helper definition (also reported, although not a theorem):
```sml
zero_head_refunds s = s with contexts :=
  (FST (HD s.contexts) with <|addRefund := 0; subRefund := 0|>,
   SND (HD s.contexts)) :: TL s.contexts
```

## spec/prop/vfmHandleStepScript.sml

```sml
Theorem pop_and_incorporate_context_length:
  1 < LENGTH s.contexts ==>
  LENGTH (SND (pop_and_incorporate_context success s)).contexts + 1 =
    LENGTH s.contexts

Theorem handle_ex_helper_length:
  s.contexts <> [] /\ handle_ex_helper e s = (r,s') ==>
  LENGTH s'.contexts =
    if LENGTH s.contexts <= 1 then LENGTH s.contexts
    else LENGTH s.contexts - 1

Theorem handle_exception_prefix_same_frame:
  s.contexts <> [] ==>
  same_frame_rel (zero_head_refunds s)
    (SND ((if e <> NONE /\ e <> SOME Reverted then
       do restore_state_gas; gasLeft <- get_gas_left; consume_gas gasLeft;
          set_return_data [] od
     else if e = SOME Reverted then restore_state_gas else return ()) s))

Theorem handle_exception_preserves_length_1:
  handle_exception e s = (q,s') /\ LENGTH s.contexts = 1 ==>
  LENGTH s'.contexts = 1

Theorem handle_create_effective_leftover:
  handle_create e s = (INR e',s1) /\ s.contexts <> [] ==>
  (FST (HD s1.contexts)).stateGasLeft = (FST (HD s.contexts)).stateGasLeft /\
  (FST (HD s1.contexts)).stateGasSpilled = (FST (HD s.contexts)).stateGasSpilled /\
  (if e' = NONE then
     (FST (HD s1.contexts)).msgParams.gasLimit - (FST (HD s1.contexts)).gasUsed
   else if e' = SOME Reverted then
     (FST (HD s1.contexts)).msgParams.gasLimit -
       ((FST (HD s1.contexts)).gasUsed -
        MIN (FST (HD s1.contexts)).stateGasSpilled (FST (HD s1.contexts)).gasUsed)
   else 0) <=
  (if e = NONE then
     (FST (HD s.contexts)).msgParams.gasLimit - (FST (HD s.contexts)).gasUsed
   else if e = SOME Reverted then
     (FST (HD s.contexts)).msgParams.gasLimit -
       ((FST (HD s.contexts)).gasUsed -
        MIN (FST (HD s.contexts)).stateGasSpilled (FST (HD s.contexts)).gasUsed)
   else 0)

Theorem handle_exception_prefix_budget:
  s.contexts <> [] /\
  (FST (HD s.contexts)).gasUsed <= (FST (HD s.contexts)).msgParams.gasLimit ==>
  ?sp. (if ~(e = NONE) /\ e <> SOME Reverted then
          do restore_state_gas; gasLeft <- get_gas_left; consume_gas gasLeft;
             set_return_data [] od
        else if e = SOME Reverted then restore_state_gas else return ()) s = (INL (),sp) /\
       TL sp.contexts = TL s.contexts /\
       LENGTH sp.contexts = LENGTH s.contexts /\
       sp.contexts <> [] /\
       (FST (HD sp.contexts)).msgParams = (FST (HD s.contexts)).msgParams /\
       (FST (HD sp.contexts)).msgParams.gasLimit -
         (FST (HD sp.contexts)).gasUsed <= frame_unused_gas (FST (HD s.contexts))

Theorem pop_and_incorporate_context_success_stack:
  s.contexts = (c,rb)::(p,rp)::tail /\
  c.msgParams.gasLimit - c.gasUsed <= p.gasUsed ==>
  ?sp. pop_and_incorporate_context b s = (INL (),sp) /\
       LENGTH sp.contexts = SUC (LENGTH tail) /\
       (FST (HD sp.contexts)).stack = p.stack
```

## spec/prop/vfmJumpDestScript.sml

```sml
Theorem preserves_all_jumpDest_NONE_get_update:
  (!c. (f c).jumpDest = c.jumpDest) ==>
  preserves_all_jumpDest_NONE
    (bind get_current_context (\c. set_current_context (f c)))

Theorem preserves_all_jumpDest_NONE_get_update_then:
  (!c. (f c).jumpDest = c.jumpDest) /\
  preserves_all_jumpDest_NONE k ==>
  preserves_all_jumpDest_NONE
    (bind get_current_context (\c. ignore_bind (set_current_context (f c)) k))
```

## spec/prop/vfmAccountFrameScript.sml

```sml
Theorem drain_state_gas_reservoir_effect[local]:
  s.contexts <> [] ==>
  drain_state_gas_reservoir s =
    (INL (FST (HD s.contexts)).stateGasLeft,
     s with contexts :=
       (FST (HD s.contexts) with stateGasLeft := 0, SND (HD s.contexts)) ::
       TL s.contexts)

Theorem create_prefix_withhold_create_gas[local]:
  preserves_when (\s. s.contexts <> [])
    (\s t. cp_rel s t /\ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys)
    withhold_create_gas

Theorem handle_exception_pop_structure_accounts[local]:
  s.contexts = (callee,callee_rb)::parent::rest /\
  handle_exception e s = (q,s') /\
  LENGTH s'.contexts < LENGTH s.contexts ==>
  (s'.rollback = s.rollback \/ s'.rollback = callee_rb) /\
  ?new_parent.
    s'.contexts = (new_parent,SND parent)::rest /\
    new_parent.msgParams = (FST parent).msgParams
```

## spec/prop/vfmAccountDeletionScript.sml

```sml
Theorem deletion_drain_state_gas_reservoir_effect[local]:
  s.contexts <> [] ==>
  drain_state_gas_reservoir s =
    (INL (FST (HD s.contexts)).stateGasLeft,
     s with contexts :=
       (FST (HD s.contexts) with stateGasLeft := 0, SND (HD s.contexts)) ::
       TL s.contexts)
```

## spec/prop/vfmRunCallScript.sml

```sml
Theorem proceed_call_saved_parent_rollback:
  proceed_call op sender address value argsOffset argsSize code stipend
               outputTo s = (r,s') /\ s.contexts <> [] ==>
  SND (HD (TL s'.contexts)) = SND (HD s.contexts)

Theorem proceed_create_saved_parent_rollback:
  proceed_create senderAddress address value code cappedGas s = (r,s') /\
  s.contexts <> [] ==>
  SND (HD (TL s'.contexts)) = SND (HD s.contexts)

Theorem handle_step_same_length_storageKeys_subset:
  outputTo_consistent s /\ handle_step e s = (r,s') /\
  LENGTH s'.contexts = LENGTH s.contexts ==>
  toSet s.rollback.accesses.storageKeys SUBSET
  toSet s'.rollback.accesses.storageKeys

Theorem step_same_length_preserves_non_accessed_storage:
  !s r s'. step s = (r,s') /\ s.contexts <> [] /\
    outputTo_consistent s /\ LENGTH s'.contexts = LENGTH s.contexts ==>
  !a k. ~fIN (SK a k) s'.rollback.accesses.storageKeys ==>
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage

Theorem proceed_call_parent_unused_gas_ok:
  proceed_call op sender address value argsOffset argsSize code stipend outputTo s = (r,s') /\
  s.contexts <> [] /\ oldGas + stipend <= (FST (HD s.contexts)).gasUsed ==>
  oldGas + frame_unused_gas (FST (HD s'.contexts)) <=
    (FST (EL 1 s'.contexts)).gasUsed

Theorem proceed_create_parent_unused_gas_ok:
  proceed_create senderAddress address value code cappedGas s = (r,s') /\
  s.contexts <> [] /\ oldGas + cappedGas <= (FST (HD s.contexts)).gasUsed ==>
  oldGas + frame_unused_gas (FST (HD s'.contexts)) <=
    (FST (EL 1 s'.contexts)).gasUsed

Theorem step_call_grow_parent_weight_ok:
  (!op sender address value argsOffset argsSize code stipend outputTo t r u b.
    proceed_call op sender address value argsOffset argsSize code stipend outputTo t = (r,u) /\
    t.contexts <> [] /\ b + stipend <= (FST (HD t.contexts)).gasUsed ==>
    b + weight (FST (HD u.contexts)) <= (FST (EL 1 u.contexts)).gasUsed) ==>
  wf_state s /\ step_call op s = (r,s') /\
  is_call op /\ (op <> Create /\ op <> Create2) /\
  s.contexts <> [] /\ LENGTH s'.contexts > LENGTH s.contexts ==>
  (FST (HD s.contexts)).gasUsed + weight (FST (HD s'.contexts)) <=
    (FST (EL 1 s'.contexts)).gasUsed

Theorem step_create_grow_parent_weight_ok:
  (!senderAddress address value code cappedGas t r u b.
    proceed_create senderAddress address value code cappedGas t = (r,u) /\
    t.contexts <> [] /\ b + cappedGas <= (FST (HD t.contexts)).gasUsed ==>
    b + weight (FST (HD u.contexts)) <= (FST (EL 1 u.contexts)).gasUsed) ==>
  wf_state s /\ step_create two s = (r,s') /\
  s.contexts <> [] /\ LENGTH s'.contexts > LENGTH s.contexts ==>
  (FST (HD s.contexts)).gasUsed + weight (FST (HD s'.contexts)) <=
    (FST (EL 1 s'.contexts)).gasUsed

Theorem step_call_grow_parent_unused_gas_ok:
  wf_state s /\ step_call op s = (r,s') /\
  is_call op /\ (op <> Create /\ op <> Create2) /\
  s.contexts <> [] /\ LENGTH s'.contexts > LENGTH s.contexts ==>
  (FST (HD s.contexts)).gasUsed + frame_unused_gas (FST (HD s'.contexts)) <=
  (FST (EL 1 s'.contexts)).gasUsed

Theorem step_create_grow_parent_unused_gas_ok:
  wf_state s /\ step_create two s = (r,s') /\
  s.contexts <> [] /\ LENGTH s'.contexts > LENGTH s.contexts ==>
  (FST (HD s.contexts)).gasUsed + frame_unused_gas (FST (HD s'.contexts)) <=
  (FST (EL 1 s'.contexts)).gasUsed

Theorem step_inner_grow_parent_unused_gas_ok:
  step_inner s = (r,s') /\ wf_state s /\ s.contexts <> [] /\
  LENGTH s'.contexts > LENGTH s.contexts ==>
  frame_unused_gas (FST (HD s'.contexts)) <= (FST (EL 1 s'.contexts)).gasUsed

Theorem step_grow_parent_unused_gas_ok:
  step s = (r,s') /\ wf_state s /\ s.contexts <> [] /\
  outputTo_consistent_stack s /\ LENGTH s'.contexts > LENGTH s.contexts ==>
  frame_unused_gas (FST (HD s'.contexts)) <= (FST (EL 1 s'.contexts)).gasUsed

Theorem step_inner_unused_gas_nonincrease:
  s.contexts <> [] /\ step_inner s = (r,s') ==>
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts)

Theorem step_unused_gas_nonincrease:
  s.contexts <> [] /\ step s = (r,s') ==>
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts)

Theorem gas_stack_ok_pop_transfer:
  gas_stack_ok s /\ s.contexts = child::parent::rest /\
  s'.contexts = new::rest /\
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts) ==>
  gas_stack_ok s'

Theorem gas_stack_ok_push_transfer:
  gas_stack_ok s /\ s.contexts = old::rest /\
  s'.contexts = child::parent::rest' /\ MAP FST rest' = MAP FST rest /\
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts) /\
  frame_unused_gas (FST child) <= (FST parent).gasUsed ==>
  gas_stack_ok s'

Theorem gas_stack_ok_same_tail_transfer:
  gas_stack_ok s /\ s.contexts <> [] /\ s'.contexts <> [] /\
  MAP FST (TL s'.contexts) = MAP FST (TL s.contexts) /\
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts) ==>
  gas_stack_ok s'
```

The original `step_preserves_non_accessed_storage`, `step_call_grow_parent_gas_ok` and `step_create_grow_parent_gas_ok` remain under their original names/statements as corollaries. The `step_inst_same_frame_unused_gas_monotone` and `step_inner_same_frame_unused_gas_monotone` names are TASK-authorized replacements, not new independent helpers.

## Historical probe theories

### spec/prop/vfmCallDrainProbeScript.sml

```sml
Theorem call_drain_destination_not_precompile:
  ~fIN (100w : address) precompile_addresses

Theorem proceed_call_push_structure_counterexample:
  !s c rb.
    let s0 = s with contexts := [(c with stateGasLeft := 1,rb)] in
    let out = proceed_call Call 0w 100w 0 0 0 [] 0
                (Memory <|offset := 0; size := 0|>) s0 in
    s0.contexts <> [] /\ FST out = INL () /\
    LENGTH (SND out).contexts = 2 /\
    (FST (HD s0.contexts)).stateGasLeft = 1 /\
    (FST (HD (TL (SND out).contexts))).stateGasLeft = 0 /\
    TL (SND out).contexts <> s0.contexts

Theorem proceed_create_push_structure_counterexample:
  !s c rb.
    let s0 = s with contexts := [(c with stateGasLeft := 1,rb)] in
    let out = proceed_create 0w 100w 0 [] 0 s0 in
    s0.contexts <> [] /\ FST out = INL () /\
    LENGTH (SND out).contexts = 2 /\
    (FST (HD s0.contexts)).stateGasLeft = 1 /\
    (FST (HD (TL (SND out).contexts))).stateGasLeft = 0 /\
    MAP FST (TL (SND out).contexts) <> MAP FST s0.contexts
```

### spec/prop/vfmGasStackProbeScript.sml

```sml
Theorem same_frame_rel_preserves_gas_stack_ok_counterexample:
  !s c p rb.
    let c0 = c with <|msgParams := c.msgParams with gasLimit := 0;
                      gasUsed := 0; stateGasSpilled := 0|> in
    let p0 = p with gasUsed := 0 in
    let s0 = s with contexts := [(c0,rb);(p0,rb)] in
    let s1 = s with contexts := [(c0 with stateGasSpilled := 1,rb);(p0,rb)] in
    same_frame_rel s0 s1 /\ gas_stack_ok s0 /\
    (FST (HD s1.contexts)).gasUsed >= (FST (HD s0.contexts)).gasUsed /\
    ~gas_stack_ok s1
```

### spec/prop/vfmSstoreGasProbeScript.sml

New probe definitions, included to make the statements self-contained:
```sml
sstore_probe_frame c = c with <|
  stack := [0w;0w]; gasUsed := 30000; stateGasSpilled := 30000;
  stateGasLeft := 0; addRefund := 0; subRefund := 0;
  msgParams := c.msgParams with <|callee := 0w; static := F;
    gasLimit := 100000; code := []; parsed := parse_code 0 FEMPTY []|>|>

sstore_probe_state s c a d = s with <|
  contexts := [(sstore_probe_frame c,s.rollback)];
  originalAccounts := K (a with storage := K 0w);
  rollback := s.rollback with <|
    accounts := K (a with storage := K 1w);
    accesses := s.rollback.accesses with storageKeys := fINSERT (SK 0w 0w) fEMPTY|>;
  msdomain := Enforce (d with storageKeys := fINSERT (SK 0w 0w) fEMPTY)|>

Theorem sstore_probe_gas_decreases:
  let s0 = sstore_probe_state s c a d in
  let out = step_inst SStore s0 in
    ISL (FST out) /\
    (FST (HD (SND out).contexts)).gasUsed <
    (FST (HD s0.contexts)).gasUsed

Theorem step_inst_same_frame_gas_monotone_counterexample:
  let s0 = sstore_probe_state s c a d in
  let out = step_inst SStore s0 in
    step_inst SStore s0 = out /\
    same_frame_rel s0 (SND out) /\
    EVERY (wf_context o FST) s0.contexts /\
    (FST (HD (SND out).contexts)).gasUsed <
    (FST (HD s0.contexts)).gasUsed
```

### spec/prop/vfmPopGasProbeScript.sml

New probe definitions:
```sml
pop_gas_child c = c with <|
  msgParams := c.msgParams with <|gasLimit := 0;
    outputTo := Memory <|offset := 0; size := 0|>|>;
  gasUsed := 0; stateGasLeft := 0; stateGasSpilled := 0;
  stateGasCommitted := 0; returnData := []|>

pop_gas_parent c = c with <|gasUsed := 1; stateGasLeft := 1;
  stateGasSpilled := 1; stack := []|>

reverted_pop_gas_child c = c with <|
  msgParams := c.msgParams with <|gasLimit := 1;
    outputTo := Memory <|offset := 0; size := 0|>|>;
  gasUsed := 1; stateGasLeft := 0; stateGasSpilled := 1;
  stateGasBaseline := 0; stateGasCommitted := 0; returnData := []|>

reverted_pop_gas_parent c = c with <|gasUsed := 2; stateGasLeft := 0;
  stateGasSpilled := 0; stack := []|>

Theorem handle_exception_pop_generic_gen_counterexample:
  !s c rb.
    let callee = pop_gas_child c in
    let parent = (pop_gas_parent c,rb) in
    let s0 = s with contexts := [(callee,rb);parent] in
    let out = handle_exception NONE s0 in
    s0.contexts = (callee,rb)::parent::[] /\
    handle_exception NONE s0 = out /\
    LENGTH (SND out).contexts < LENGTH s0.contexts /\
    ~(((SND out).rollback = s0.rollback \/ (SND out).rollback = rb) /\
      ?new_parent_ctx.
        (SND out).contexts = [(new_parent_ctx,SND parent)] /\
        new_parent_ctx.msgParams = (FST parent).msgParams /\
        new_parent_ctx.gasUsed >= (FST parent).gasUsed -
          (callee.msgParams.gasLimit - callee.gasUsed))

Theorem handle_exception_reverted_pop_generic_gen_counterexample:
  !s c rb.
    let callee = reverted_pop_gas_child c in
    let parent = (reverted_pop_gas_parent c,rb) in
    let s0 = s with contexts := [(callee,rb);parent] in
    let out = handle_exception (SOME Reverted) s0 in
    s0.contexts = (callee,rb)::parent::[] /\
    handle_exception (SOME Reverted) s0 = out /\
    LENGTH (SND out).contexts < LENGTH s0.contexts /\
    ~(((SND out).rollback = s0.rollback \/ (SND out).rollback = rb) /\
      ?new_parent_ctx.
        (SND out).contexts = [(new_parent_ctx,SND parent)] /\
        new_parent_ctx.msgParams = (FST parent).msgParams /\
        new_parent_ctx.gasUsed >= (FST parent).gasUsed -
          (callee.msgParams.gasLimit - callee.gasUsed) -
          MIN ((FST parent).stateGasLeft + callee.stateGasLeft)
              ((FST parent).stateGasSpilled + callee.stateGasSpilled))

Theorem handle_exception_pop_generic_gen_corrected_instance:
  !s c rb.
    let callee = pop_gas_child c in
    let parent = (pop_gas_parent c,rb) in
    let s0 = s with contexts := [(callee,rb);parent] in
    let out = handle_exception NONE s0 in
    let leftAfter = callee.msgParams.gasLimit - callee.gasUsed in
    s0.contexts = (callee,rb)::parent::[] /\
    handle_exception NONE s0 = out /\
    LENGTH (SND out).contexts < LENGTH s0.contexts /\
    ((SND out).rollback = s0.rollback \/ (SND out).rollback = rb) /\
    ?new_parent_ctx.
      (SND out).contexts = [(new_parent_ctx,SND parent)] /\
      new_parent_ctx.msgParams = (FST parent).msgParams /\
      new_parent_ctx.gasUsed >= (FST parent).gasUsed - leftAfter -
        MIN ((FST parent).stateGasLeft + callee.stateGasLeft)
            ((FST parent).stateGasSpilled + callee.stateGasSpilled)

Theorem handle_exception_reverted_pop_generic_gen_corrected_instance:
  !s c rb.
    let callee = reverted_pop_gas_child c in
    let parent = (reverted_pop_gas_parent c,rb) in
    let s0 = s with contexts := [(callee,rb);parent] in
    let out = handle_exception (SOME Reverted) s0 in
    let leftAfter = callee.msgParams.gasLimit -
      (callee.gasUsed - MIN callee.stateGasSpilled callee.gasUsed) in
    s0.contexts = (callee,rb)::parent::[] /\
    handle_exception (SOME Reverted) s0 = out /\
    LENGTH (SND out).contexts < LENGTH s0.contexts /\
    ((SND out).rollback = s0.rollback \/ (SND out).rollback = rb) /\
    ?new_parent_ctx.
      (SND out).contexts = [(new_parent_ctx,SND parent)] /\
      new_parent_ctx.msgParams = (FST parent).msgParams /\
      new_parent_ctx.gasUsed >= (FST parent).gasUsed - leftAfter -
        MIN ((FST parent).stateGasLeft + callee.stateGasLeft)
            ((FST parent).stateGasSpilled + callee.stateGasSpilled)
```

## Files with no new lemma

`spec/prop/vfmStepLengthScript.sml`, `tests/vfmOriginalAccountsScript.sml`, `tests/vfmSettlementScript.sml`: proof/fixture changes only, no new theorem names. `preserves_rollback_unuse_gas` in StoragePredicates was relocated, not added.
