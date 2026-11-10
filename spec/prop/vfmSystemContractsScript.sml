Theory vfmSystemContracts
Ancestors vfmCompute vfmExecution vfmTypes vfmConstants vfmOperation
Libs cv_transLib wordsLib

(* https://eips.ethereum.org/EIPS/eip-4788: canonical runtime. *)
Definition beacon_roots_code_def:
  beacon_roots_code : byte list = [
    0x33w; 0x73w; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xfew; 0x14w; 0x60w;
    0x4dw; 0x57w; 0x60w; 0x20w; 0x36w; 0x14w; 0x60w; 0x24w; 0x57w; 0x5fw; 0x5fw; 0xfdw;
    0x5bw; 0x5fw; 0x35w; 0x80w; 0x15w; 0x60w; 0x49w; 0x57w; 0x62w; 0x00w; 0x1fw; 0xffw;
    0x81w; 0x06w; 0x90w; 0x81w; 0x54w; 0x14w; 0x60w; 0x3cw; 0x57w; 0x5fw; 0x5fw; 0xfdw;
    0x5bw; 0x62w; 0x00w; 0x1fw; 0xffw; 0x01w; 0x54w; 0x5fw; 0x52w; 0x60w; 0x20w; 0x5fw;
    0xf3w; 0x5bw; 0x5fw; 0x5fw; 0xfdw; 0x5bw; 0x62w; 0x00w; 0x1fw; 0xffw; 0x42w; 0x06w;
    0x42w; 0x81w; 0x55w; 0x5fw; 0x35w; 0x90w; 0x62w; 0x00w; 0x1fw; 0xffw; 0x01w; 0x55w;
    0x00w]
End
val () = cv_auto_trans beacon_roots_code_def;

(* https://eips.ethereum.org/EIPS/eip-2935: canonical runtime. *)
Definition history_storage_code_def:
  history_storage_code : byte list = [
    0x33w; 0x73w; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xfew; 0x14w; 0x60w;
    0x46w; 0x57w; 0x60w; 0x20w; 0x36w; 0x03w; 0x60w; 0x42w; 0x57w; 0x5fw; 0x35w; 0x60w;
    0x01w; 0x43w; 0x03w; 0x81w; 0x11w; 0x60w; 0x42w; 0x57w; 0x61w; 0x1fw; 0xffw; 0x81w;
    0x43w; 0x03w; 0x11w; 0x60w; 0x42w; 0x57w; 0x61w; 0x1fw; 0xffw; 0x90w; 0x06w; 0x54w;
    0x5fw; 0x52w; 0x60w; 0x20w; 0x5fw; 0xf3w; 0x5bw; 0x5fw; 0x5fw; 0xfdw; 0x5bw; 0x5fw;
    0x35w; 0x61w; 0x1fw; 0xffw; 0x60w; 0x01w; 0x43w; 0x03w; 0x06w; 0x55w; 0x00w]
End
val () = cv_auto_trans history_storage_code_def;

(* https://eips.ethereum.org/EIPS/eip-7002: canonical runtime. *)
Definition withdrawal_request_code_def:
  withdrawal_request_code : byte list = [
    0x33w; 0x73w; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xfew; 0x14w; 0x60w;
    0xcbw; 0x57w; 0x60w; 0x11w; 0x5fw; 0x54w; 0x80w; 0x7fw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0x14w; 0x61w; 0x01w; 0xf4w; 0x57w; 0x60w; 0x01w; 0x82w;
    0x02w; 0x60w; 0x01w; 0x90w; 0x5fw; 0x5bw; 0x5fw; 0x82w; 0x11w; 0x15w; 0x60w; 0x68w;
    0x57w; 0x81w; 0x01w; 0x90w; 0x83w; 0x02w; 0x84w; 0x83w; 0x02w; 0x90w; 0x04w; 0x91w;
    0x60w; 0x01w; 0x01w; 0x91w; 0x90w; 0x60w; 0x4dw; 0x56w; 0x5bw; 0x90w; 0x93w; 0x90w;
    0x04w; 0x92w; 0x50w; 0x50w; 0x50w; 0x36w; 0x60w; 0x38w; 0x14w; 0x60w; 0x88w; 0x57w;
    0x36w; 0x61w; 0x01w; 0xf4w; 0x57w; 0x34w; 0x61w; 0x01w; 0xf4w; 0x57w; 0x5fw; 0x52w;
    0x60w; 0x20w; 0x5fw; 0xf3w; 0x5bw; 0x34w; 0x10w; 0x61w; 0x01w; 0xf4w; 0x57w; 0x60w;
    0x01w; 0x54w; 0x60w; 0x01w; 0x01w; 0x60w; 0x01w; 0x55w; 0x60w; 0x03w; 0x54w; 0x80w;
    0x60w; 0x03w; 0x02w; 0x60w; 0x04w; 0x01w; 0x33w; 0x81w; 0x55w; 0x60w; 0x01w; 0x01w;
    0x5fw; 0x35w; 0x81w; 0x55w; 0x60w; 0x01w; 0x01w; 0x60w; 0x20w; 0x35w; 0x90w; 0x55w;
    0x33w; 0x60w; 0x60w; 0x1bw; 0x5fw; 0x52w; 0x60w; 0x38w; 0x5fw; 0x60w; 0x14w; 0x37w;
    0x60w; 0x4cw; 0x5fw; 0xa0w; 0x60w; 0x01w; 0x01w; 0x60w; 0x03w; 0x55w; 0x00w; 0x5bw;
    0x60w; 0x03w; 0x54w; 0x60w; 0x02w; 0x54w; 0x80w; 0x82w; 0x03w; 0x80w; 0x60w; 0x10w;
    0x11w; 0x60w; 0xdfw; 0x57w; 0x50w; 0x60w; 0x10w; 0x5bw; 0x5fw; 0x5bw; 0x81w; 0x81w;
    0x14w; 0x61w; 0x01w; 0x83w; 0x57w; 0x82w; 0x81w; 0x01w; 0x60w; 0x03w; 0x02w; 0x60w;
    0x04w; 0x01w; 0x81w; 0x60w; 0x4cw; 0x02w; 0x81w; 0x54w; 0x60w; 0x60w; 0x1bw; 0x81w;
    0x52w; 0x60w; 0x14w; 0x01w; 0x81w; 0x60w; 0x01w; 0x01w; 0x54w; 0x81w; 0x52w; 0x60w;
    0x20w; 0x01w; 0x90w; 0x60w; 0x02w; 0x01w; 0x54w; 0x80w; 0x7fw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0x00w; 0x00w; 0x00w; 0x00w; 0x00w; 0x00w; 0x00w; 0x00w; 0x00w; 0x00w; 0x00w;
    0x00w; 0x00w; 0x00w; 0x00w; 0x00w; 0x16w; 0x82w; 0x52w; 0x90w; 0x60w; 0x10w; 0x01w;
    0x90w; 0x60w; 0x40w; 0x1cw; 0x90w; 0x81w; 0x60w; 0x38w; 0x1cw; 0x81w; 0x60w; 0x07w;
    0x01w; 0x53w; 0x81w; 0x60w; 0x30w; 0x1cw; 0x81w; 0x60w; 0x06w; 0x01w; 0x53w; 0x81w;
    0x60w; 0x28w; 0x1cw; 0x81w; 0x60w; 0x05w; 0x01w; 0x53w; 0x81w; 0x60w; 0x20w; 0x1cw;
    0x81w; 0x60w; 0x04w; 0x01w; 0x53w; 0x81w; 0x60w; 0x18w; 0x1cw; 0x81w; 0x60w; 0x03w;
    0x01w; 0x53w; 0x81w; 0x60w; 0x10w; 0x1cw; 0x81w; 0x60w; 0x02w; 0x01w; 0x53w; 0x81w;
    0x60w; 0x08w; 0x1cw; 0x81w; 0x60w; 0x01w; 0x01w; 0x53w; 0x53w; 0x60w; 0x01w; 0x01w;
    0x60w; 0xe1w; 0x56w; 0x5bw; 0x91w; 0x01w; 0x80w; 0x92w; 0x14w; 0x61w; 0x01w; 0x95w;
    0x57w; 0x90w; 0x60w; 0x02w; 0x55w; 0x61w; 0x01w; 0xa0w; 0x56w; 0x5bw; 0x90w; 0x50w;
    0x5fw; 0x60w; 0x02w; 0x55w; 0x5fw; 0x60w; 0x03w; 0x55w; 0x5bw; 0x5fw; 0x54w; 0x80w;
    0x7fw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0x14w; 0x15w; 0x61w;
    0x01w; 0xcdw; 0x57w; 0x50w; 0x5fw; 0x5bw; 0x60w; 0x01w; 0x54w; 0x60w; 0x02w; 0x82w;
    0x82w; 0x01w; 0x11w; 0x61w; 0x01w; 0xe2w; 0x57w; 0x50w; 0x50w; 0x5fw; 0x61w; 0x01w;
    0xe8w; 0x56w; 0x5bw; 0x01w; 0x60w; 0x02w; 0x90w; 0x03w; 0x5bw; 0x5fw; 0x55w; 0x5fw;
    0x60w; 0x01w; 0x55w; 0x60w; 0x4cw; 0x02w; 0x5fw; 0xf3w; 0x5bw; 0x5fw; 0x5fw; 0xfdw]
End
val () = cv_auto_trans withdrawal_request_code_def;

(* https://eips.ethereum.org/EIPS/eip-7251: canonical runtime. *)
Definition consolidation_request_code_def:
  consolidation_request_code : byte list = [
    0x33w; 0x73w; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xfew; 0x14w; 0x60w;
    0xd3w; 0x57w; 0x60w; 0x11w; 0x5fw; 0x54w; 0x80w; 0x7fw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0x14w; 0x61w; 0x01w; 0x9aw; 0x57w; 0x60w; 0x01w; 0x82w;
    0x02w; 0x60w; 0x01w; 0x90w; 0x5fw; 0x5bw; 0x5fw; 0x82w; 0x11w; 0x15w; 0x60w; 0x68w;
    0x57w; 0x81w; 0x01w; 0x90w; 0x83w; 0x02w; 0x84w; 0x83w; 0x02w; 0x90w; 0x04w; 0x91w;
    0x60w; 0x01w; 0x01w; 0x91w; 0x90w; 0x60w; 0x4dw; 0x56w; 0x5bw; 0x90w; 0x93w; 0x90w;
    0x04w; 0x92w; 0x50w; 0x50w; 0x50w; 0x36w; 0x60w; 0x60w; 0x14w; 0x60w; 0x88w; 0x57w;
    0x36w; 0x61w; 0x01w; 0x9aw; 0x57w; 0x34w; 0x61w; 0x01w; 0x9aw; 0x57w; 0x5fw; 0x52w;
    0x60w; 0x20w; 0x5fw; 0xf3w; 0x5bw; 0x34w; 0x10w; 0x61w; 0x01w; 0x9aw; 0x57w; 0x60w;
    0x01w; 0x54w; 0x60w; 0x01w; 0x01w; 0x60w; 0x01w; 0x55w; 0x60w; 0x03w; 0x54w; 0x80w;
    0x60w; 0x04w; 0x02w; 0x60w; 0x04w; 0x01w; 0x33w; 0x81w; 0x55w; 0x60w; 0x01w; 0x01w;
    0x5fw; 0x35w; 0x81w; 0x55w; 0x60w; 0x01w; 0x01w; 0x60w; 0x20w; 0x35w; 0x81w; 0x55w;
    0x60w; 0x01w; 0x01w; 0x60w; 0x40w; 0x35w; 0x90w; 0x55w; 0x33w; 0x60w; 0x60w; 0x1bw;
    0x5fw; 0x52w; 0x60w; 0x60w; 0x5fw; 0x60w; 0x14w; 0x37w; 0x60w; 0x74w; 0x5fw; 0xa0w;
    0x60w; 0x01w; 0x01w; 0x60w; 0x03w; 0x55w; 0x00w; 0x5bw; 0x60w; 0x03w; 0x54w; 0x60w;
    0x02w; 0x54w; 0x80w; 0x82w; 0x03w; 0x80w; 0x60w; 0x02w; 0x11w; 0x60w; 0xe7w; 0x57w;
    0x50w; 0x60w; 0x02w; 0x5bw; 0x5fw; 0x5bw; 0x81w; 0x81w; 0x14w; 0x61w; 0x01w; 0x29w;
    0x57w; 0x82w; 0x81w; 0x01w; 0x60w; 0x04w; 0x02w; 0x60w; 0x04w; 0x01w; 0x81w; 0x60w;
    0x74w; 0x02w; 0x81w; 0x54w; 0x60w; 0x60w; 0x1bw; 0x81w; 0x52w; 0x60w; 0x14w; 0x01w;
    0x81w; 0x60w; 0x01w; 0x01w; 0x54w; 0x81w; 0x52w; 0x60w; 0x20w; 0x01w; 0x81w; 0x60w;
    0x02w; 0x01w; 0x54w; 0x81w; 0x52w; 0x60w; 0x20w; 0x01w; 0x90w; 0x60w; 0x03w; 0x01w;
    0x54w; 0x90w; 0x52w; 0x60w; 0x01w; 0x01w; 0x60w; 0xe9w; 0x56w; 0x5bw; 0x91w; 0x01w;
    0x80w; 0x92w; 0x14w; 0x61w; 0x01w; 0x3bw; 0x57w; 0x90w; 0x60w; 0x02w; 0x55w; 0x61w;
    0x01w; 0x46w; 0x56w; 0x5bw; 0x90w; 0x50w; 0x5fw; 0x60w; 0x02w; 0x55w; 0x5fw; 0x60w;
    0x03w; 0x55w; 0x5bw; 0x5fw; 0x54w; 0x80w; 0x7fw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw; 0xffw;
    0xffw; 0xffw; 0xffw; 0x14w; 0x15w; 0x61w; 0x01w; 0x73w; 0x57w; 0x50w; 0x5fw; 0x5bw;
    0x60w; 0x01w; 0x54w; 0x60w; 0x01w; 0x82w; 0x82w; 0x01w; 0x11w; 0x61w; 0x01w; 0x88w;
    0x57w; 0x50w; 0x50w; 0x5fw; 0x61w; 0x01w; 0x8ew; 0x56w; 0x5bw; 0x01w; 0x60w; 0x01w;
    0x90w; 0x03w; 0x5bw; 0x5fw; 0x55w; 0x5fw; 0x60w; 0x01w; 0x55w; 0x60w; 0x74w; 0x02w;
    0x5fw; 0xf3w; 0x5bw; 0x5fw; 0x5fw; 0xfdw]
End
val () = cv_auto_trans consolidation_request_code_def;

(* Deployment starts with an inhibitor in the excess slot. The first system
   call clears it while retaining this block's additions in the fee update. *)
Definition request_inhibitor_accounts_def:
  request_inhibitor_accounts address code =
    update_account address
      (empty_account_state with <| code := code; nonce := 1;
        storage := update_storage 0w (n2w (2 ** 256 - 1))
                     (update_storage 1w 3w empty_storage) |>) empty_accounts
End
val () = cv_auto_trans request_inhibitor_accounts_def;

Definition request_queue_metadata_def:
  request_queue_metadata address accounts =
    MAP (λkey. lookup_storage key (lookup_account address accounts).storage)
      [0w; 1w; 2w; 3w]
End
val () = cv_auto_trans request_queue_metadata_def;

Theorem withdrawal_inhibitor_model:
  request_queue_metadata withdrawal_request_contract
    (SND (dequeue_withdrawal_requests
      (request_inhibitor_accounts withdrawal_request_contract withdrawal_request_code))) =
  [1w; 0w; 0w; 0w]
Proof
  CONV_TAC cv_eval
QED

Theorem consolidation_inhibitor_model:
  request_queue_metadata consolidation_request_contract
    (SND (dequeue_consolidation_requests
      (request_inhibitor_accounts consolidation_request_contract consolidation_request_code))) =
  [2w; 0w; 0w; 0w]
Proof
  CONV_TAC cv_eval
QED

Theorem system_dispatch_caller[local]:
  s.contexts = (c, rb)::cs /\
  FLOOKUP c.msgParams.parsed c.pc = SOME Caller /\
  c.jumpDest = NONE /\ LENGTH c.stack < stack_limit /\
  c.gasUsed + 2 <= c.msgParams.gasLimit ==>
  step s = (INL (), s with contexts :=
    (c with <| stack := w2w c.msgParams.caller :: c.stack;
               gasUsed := c.gasUsed + 2; pc := c.pc + 1 |>, rb)::cs)
Proof
  rpt strip_tac >> gvs[stack_limit_def] >>
  simp[step_def, step_inst_def, step_msgParams_def, step_context_def,
       consume_gas_def, push_stack_def, inc_pc_or_jump_def, is_call_def,
       static_gas_def, opcode_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, handle_def]
QED

Theorem system_dispatch_push[local]:
  FLOOKUP c.msgParams.parsed c.pc = SOME (Push n ws) /\
  c.jumpDest = NONE /\ LENGTH c.stack < stack_limit /\
  c.gasUsed + static_gas (Push n ws) <= c.msgParams.gasLimit ==>
  step (s with contexts := (c, rb)::cs) = (INL (), s with contexts :=
    (c with <| stack := word_of_bytes F 0w (REVERSE ws) :: c.stack;
               gasUsed := c.gasUsed + static_gas (Push n ws);
               pc := c.pc + LENGTH (opcode (Push n ws)) |>, rb)::cs)
Proof
  rpt strip_tac >> gvs[stack_limit_def] >>
  simp[step_def, step_inst_def, step_push_def,
       consume_gas_def, push_stack_def, inc_pc_or_jump_def, is_call_def,
       get_current_context_def, set_current_context_def, bind_def,
       ignore_bind_def, return_def, assert_def, handle_def, stack_limit_def]
QED

Theorem system_dispatch_eq[local]:
  c.stack = x::y::ss /\
  FLOOKUP c.msgParams.parsed c.pc = SOME Eq /\
  c.jumpDest = NONE /\ LENGTH ss < stack_limit /\
  c.gasUsed + 3 <= c.msgParams.gasLimit ==>
  step (s with contexts := (c, rb)::cs) = (INL (), s with contexts :=
    (c with <| stack := b2w (x = y) :: ss;
               gasUsed := c.gasUsed + 3; pc := c.pc + 1 |>, rb)::cs)
Proof
  rpt strip_tac >> gvs[stack_limit_def] >>
  simp[step_def, step_inst_def, step_binop_def, pop_stack_def,
       consume_gas_def, push_stack_def, inc_pc_or_jump_def, is_call_def,
       static_gas_def, opcode_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, handle_def, stack_limit_def]
QED

Theorem system_dispatch_jumpi[local]:
  c.stack = dest::cond::ss /\ cond <> 0w /\
  FLOOKUP c.msgParams.parsed c.pc = SOME JumpI /\
  FLOOKUP c.msgParams.parsed (w2n dest) = SOME JumpDest /\
  w2n dest < LENGTH c.msgParams.code /\
  c.gasUsed + 10 <= c.msgParams.gasLimit ==>
  step (s with contexts := (c, rb)::cs) = (INL (), s with contexts :=
    (c with <| stack := ss; jumpDest := NONE;
               gasUsed := c.gasUsed + 10; pc := w2n dest |>, rb)::cs)
Proof
  rpt strip_tac >>
  simp[step_def, step_inst_def, step_jumpi_def, pop_stack_def,
       consume_gas_def, set_jump_dest_def, inc_pc_or_jump_def, is_call_def,
       static_gas_def, opcode_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, handle_def]
QED

Theorem system_run_step[local]:
  step s = (INL (), t) ==> run s = run t
Proof
  strip_tac >> simp[vfmDecreasesGasTheory.run_eq_tr] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def]
QED

Theorem system_privileged_dispatch_cert[local]:
  s.contexts = (c, rb)::cs /\ c.pc = 0 /\ c.stack = [] /\
  c.jumpDest = NONE /\ c.gasUsed + 21 <= c.msgParams.gasLimit /\
  FLOOKUP c.msgParams.parsed 0 = SOME Caller /\
  FLOOKUP c.msgParams.parsed 1 = SOME (Push 20 caller_bytes) /\
  LENGTH caller_bytes = 20 /\
  word_of_bytes F 0w (REVERSE caller_bytes) = (w2w c.msgParams.caller : bytes32) /\
  FLOOKUP c.msgParams.parsed 22 = SOME Eq /\
  FLOOKUP c.msgParams.parsed 23 = SOME (Push 1 [dest]) /\
  FLOOKUP c.msgParams.parsed 25 = SOME JumpI /\
  FLOOKUP c.msgParams.parsed (w2n dest) = SOME JumpDest /\
  w2n dest < LENGTH c.msgParams.code ==>
  FUNPOW (step o SND) 5 (INL (), s) =
    (INL (), s with contexts :=
      (c with <| pc := w2n dest; gasUsed := c.gasUsed + 21 |>, rb)::cs) /\
  run s = run (s with contexts :=
      (c with <| pc := w2n dest; gasUsed := c.gasUsed + 21 |>, rb)::cs)
Proof
  rpt strip_tac >>
  `word_of_bytes F 0w [dest] = (w2w dest : bytes32)` by
    (simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
          byteTheory.byte_index_def, byteTheory.word_slice_alt_zero]) >>
  qabbrev_tac `c1 = c with <|stack := w2w c.msgParams.caller :: c.stack;
    gasUsed := c.gasUsed + 2; pc := c.pc + 1|>` >>
  `step s = (INL (), s with contexts := (c1, rb)::cs)` by
    (simp[Abbr `c1`] >> drule system_dispatch_caller >> simp[stack_limit_def]) >>
  qabbrev_tac `c2 = c1 with <|
    stack := word_of_bytes F 0w (REVERSE caller_bytes) :: c1.stack;
    gasUsed := c1.gasUsed + static_gas (Push 20 caller_bytes);
    pc := c1.pc + LENGTH (opcode (Push 20 caller_bytes))|>` >>
  `step (s with contexts := (c1, rb)::cs) =
     (INL (), s with contexts := (c2, rb)::cs)` by
    (simp_tac pure_ss [Abbr `c2`] >> irule system_dispatch_push >>
     simp[Abbr `c1`, stack_limit_def, static_gas_def]) >>
  qabbrev_tac `c3 = c2 with <|
    stack := b2w ((w2w c.msgParams.caller : bytes32) = w2w c.msgParams.caller) :: [];
    gasUsed := c2.gasUsed + 3; pc := c2.pc + 1|>` >>
  `step (s with contexts := (c2, rb)::cs) =
     (INL (), s with contexts := (c3, rb)::cs)` by
    (simp_tac pure_ss [Abbr `c3`] >> irule system_dispatch_eq >>
     simp[Abbr `c2`, Abbr `c1`, stack_limit_def, static_gas_def, opcode_def]) >>
  qabbrev_tac `c4 = c3 with <|
    stack := word_of_bytes F 0w (REVERSE [dest]) :: c3.stack;
    gasUsed := c3.gasUsed + static_gas (Push 1 [dest]);
    pc := c3.pc + LENGTH (opcode (Push 1 [dest]))|>` >>
  `step (s with contexts := (c3, rb)::cs) =
     (INL (), s with contexts := (c4, rb)::cs)` by
    (simp_tac pure_ss [Abbr `c4`] >> irule system_dispatch_push >>
     simp[Abbr `c3`, Abbr `c2`, Abbr `c1`, stack_limit_def, static_gas_def,
          opcode_def]) >>
  `step (s with contexts := (c4, rb)::cs) =
     (INL (), s with contexts :=
       (c4 with <| stack := []; jumpDest := NONE;
         gasUsed := c4.gasUsed + 10;
         pc := w2n (word_of_bytes F 0w (REVERSE [dest]) : bytes32) |>, rb)::cs)` by
    (irule system_dispatch_jumpi >>
     simp[Abbr `c4`, Abbr `c3`, Abbr `c2`, Abbr `c1`,
          static_gas_def, opcode_def, wordsTheory.w2n_w2w]) >>
  imp_res_tac system_run_step >>
  simp[numeralTheory.numeral_funpow] >>
  simp[Abbr `c4`, Abbr `c3`, Abbr `c2`, Abbr `c1`,
       static_gas_def, opcode_def, wordsTheory.w2n_w2w] >>
  Cases_on `c` >> gvs[vfmContextTheory.context_fn_updates]
QED

Theorem system_privileged_dispatch:
  s.contexts = (c, rb)::cs /\ c.pc = 0 /\ c.stack = [] /\
  c.jumpDest = NONE /\ c.gasUsed + 21 <= c.msgParams.gasLimit /\
  FLOOKUP c.msgParams.parsed 0 = SOME Caller /\
  FLOOKUP c.msgParams.parsed 1 = SOME (Push 20 caller_bytes) /\
  LENGTH caller_bytes = 20 /\
  word_of_bytes F 0w (REVERSE caller_bytes) = (w2w c.msgParams.caller : bytes32) /\
  FLOOKUP c.msgParams.parsed 22 = SOME Eq /\
  FLOOKUP c.msgParams.parsed 23 = SOME (Push 1 [dest]) /\
  FLOOKUP c.msgParams.parsed 25 = SOME JumpI /\
  FLOOKUP c.msgParams.parsed (w2n dest) = SOME JumpDest /\
  w2n dest < LENGTH c.msgParams.code ==>
  FUNPOW (step o SND) 5 (INL (), s) =
    (INL (), s with contexts :=
      (c with <| pc := w2n dest; gasUsed := c.gasUsed + 21 |>, rb)::cs)
Proof
  metis_tac[system_privileged_dispatch_cert]
QED

Theorem system_privileged_dispatch_run:
  s.contexts = (c, rb)::cs /\ c.pc = 0 /\ c.stack = [] /\
  c.jumpDest = NONE /\ c.gasUsed + 21 <= c.msgParams.gasLimit /\
  FLOOKUP c.msgParams.parsed 0 = SOME Caller /\
  FLOOKUP c.msgParams.parsed 1 = SOME (Push 20 caller_bytes) /\
  LENGTH caller_bytes = 20 /\
  word_of_bytes F 0w (REVERSE caller_bytes) = (w2w c.msgParams.caller : bytes32) /\
  FLOOKUP c.msgParams.parsed 22 = SOME Eq /\
  FLOOKUP c.msgParams.parsed 23 = SOME (Push 1 [dest]) /\
  FLOOKUP c.msgParams.parsed 25 = SOME JumpI /\
  FLOOKUP c.msgParams.parsed (w2n dest) = SOME JumpDest /\
  w2n dest < LENGTH c.msgParams.code ==>
  run s = run (s with contexts :=
      (c with <| pc := w2n dest; gasUsed := c.gasUsed + 21 |>, rb)::cs)
Proof
  metis_tac[system_privileged_dispatch_cert]
QED

Definition beacon_roots_caller_word_def:
  beacon_roots_caller_word : bytes32 =
    word_of_bytes F 0w (REVERSE (TAKE 20 (DROP 2 beacon_roots_code)))
End
val () = cv_auto_trans (REWRITE_RULE [GSYM byteTheory.word_of_bytes_le_def]
  beacon_roots_caller_word_def);

Theorem beacon_roots_caller_word[local]:
  beacon_roots_caller_word = (w2w system_address : bytes32)
Proof
  CONV_TAC cv_eval
QED

Definition beacon_roots_instruction_def:
  beacon_roots_instruction pc =
    FLOOKUP (parse_code 0 FEMPTY beacon_roots_code) pc
End
val () = cv_auto_trans beacon_roots_instruction_def;

Theorem beacon_roots_parse[local]:
  beacon_roots_instruction 0 = SOME Caller /\
  beacon_roots_instruction 1 = SOME (Push 20 (TAKE 20 (DROP 2 beacon_roots_code))) /\
  beacon_roots_instruction 22 = SOME Eq /\
  beacon_roots_instruction 23 = SOME (Push 1 [0x4dw]) /\
  beacon_roots_instruction 25 = SOME JumpI /\
  beacon_roots_instruction 77 = SOME JumpDest /\
  beacon_roots_instruction 78 = SOME (Push 3 [0w; 0x1fw; 0xffw]) /\
  beacon_roots_instruction 82 = SOME TimeStamp /\
  beacon_roots_instruction 83 = SOME Mod /\
  beacon_roots_instruction 84 = SOME TimeStamp /\
  beacon_roots_instruction 85 = SOME (Dup 1) /\
  beacon_roots_instruction 86 = SOME SStore /\
  beacon_roots_instruction 87 = SOME (Push 0 []) /\
  beacon_roots_instruction 88 = SOME CallDataLoad /\
  beacon_roots_instruction 89 = SOME (Swap 0) /\
  beacon_roots_instruction 90 = SOME (Push 3 [0w; 0x1fw; 0xffw]) /\
  beacon_roots_instruction 94 = SOME Add /\
  beacon_roots_instruction 95 = SOME SStore /\
  beacon_roots_instruction 96 = SOME Stop
Proof
  rpt conj_tac >> CONV_TAC cv_eval
QED

Theorem system_jumpdest_run[local]:
  FLOOKUP c.msgParams.parsed c.pc = SOME JumpDest /\
  c.jumpDest = NONE /\ c.gasUsed + 1 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|pc := c.pc + 1; gasUsed := c.gasUsed + 1|>, rb)::cs)
Proof
  strip_tac >> irule system_run_step >>
  simp[step_def, step_inst_def, consume_gas_def, inc_pc_or_jump_def,
       is_call_def, static_gas_def, opcode_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, handle_def]
QED

Theorem system_stop_run[local]:
  FLOOKUP c.msgParams.parsed c.pc = SOME Stop /\
  c.msgParams.outputTo = empty_return_destination ==>
  run (s with contexts := [(c, rb)]) =
    SOME (INR NONE, s with contexts := [(c with returnData := [], rb)])
Proof
  strip_tac >>
  simp[vfmDecreasesGasTheory.run_eq_tr] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def, step_def, step_inst_def,
    set_return_data_def, get_current_context_def, set_current_context_def,
    bind_def, ignore_bind_def, return_def, finish_def, handle_def,
    handle_step_def, vfm_abort_def, handle_create_def, handle_exception_def,
    get_return_data_def, get_output_to_def, get_num_contexts_def,
    reraise_def, vfmContextTheory.empty_return_destination_def] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def]
QED

Theorem system_sstore_run[local]:
  c.stack = key::value::ss /\ c.jumpDest = NONE /\ ~c.msgParams.static /\
  FLOOKUP c.msgParams.parsed c.pc = SOME SStore /\ s.msdomain = Collect d /\
  address = c.msgParams.callee /\
  current = lookup_storage key (lookup_account address s.rollback.accounts).storage /\
  original = lookup_storage key (lookup_account address s.originalAccounts).storage /\
  cost = sstore_base_gas original current value +
    zero_warm (if fIN (SK address key) s.rollback.accesses.storageKeys
               then warm_access_cost else cold_sload_cost) /\
  (ad, su) = sstore_refund_updates original current value /\
  call_stipend < c.msgParams.gasLimit - c.gasUsed /\
  c.gasUsed + cost <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) =
  run (s with <|
    contexts := (c with <|pc := c.pc + 1; stack := ss;
      gasUsed := c.gasUsed + cost; addRefund := ad + c.addRefund;
      subRefund := su + c.subRefund|>, rb)::cs;
    rollback := s.rollback with <|
      accounts := update_account address
        ((lookup_account address s.rollback.accounts) with storage updated_by
          update_storage key value) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys updated_by fINSERT (SK address key)|>;
    msdomain := Collect (d with storageKeys updated_by fINSERT (SK address key))|>)
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `(ad, su) = _` (assume_tac o SYM) >>
  irule system_run_step >>
  simp[step_def, step_inst_def, step_sstore_def, step_sstore_gas_consumption_def,
       get_gas_left_def, get_callee_def, get_accounts_def, get_original_def,
       access_slot_def, domain_check_def, set_domain_def, update_gas_refund_def,
       assert_not_static_def, get_static_def, write_storage_def, update_accounts_def,
       consume_gas_def, pop_stack_def, inc_pc_or_jump_def,
       is_call_def, opcode_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, handle_def] >>
  Cases_on `c` >> Cases_on `s.rollback.accesses` >> Cases_on `s.rollback` >>
  gvs[vfmContextTheory.context_fn_updates,
      vfmContextTheory.rollback_state_fn_updates,
      vfmContextTheory.access_sets_fn_updates]
QED

Theorem beacon_roots_index_run[local]:
  c.pc = 78 /\ c.stack = [] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY beacon_roots_code /\
  c.gasUsed + 15 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) =
  run (s with contexts :=
    (c with <| pc := 86; gasUsed := c.gasUsed + 15;
       stack := [with_zero word_mod (n2w s.txParams.blockTimeStamp) 8191w;
                 n2w s.txParams.blockTimeStamp;
                 with_zero word_mod (n2w s.txParams.blockTimeStamp) 8191w] |>, rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w (REVERSE [0w; 0x1fw; 0xffw]) = (8191w : bytes32)` by
    (simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
          byteTheory.byte_index_def, byteTheory.word_slice_alt_zero,
          byteTheory.word_slice_alt_shift, byteTheory.word_slice_alt_empty]) >>
  simp[vfmDecreasesGasTheory.run_eq_tr] >>
  ntac 5 (simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_txParams_def,
    step_binop_def, step_dup_def, get_tx_params_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse])
QED

Theorem beacon_roots_data_run[local]:
  c.pc = 87 /\ c.stack = [key] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY beacon_roots_code /\
  c.gasUsed + 14 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) =
  run (s with contexts :=
    (c with <|pc := 95; gasUsed := c.gasUsed + 14;
      stack := [8191w + key;
        word_of_bytes F 0w (REVERSE (take_pad_0 32 (buffer_to_list c.msgParams.data)))]|>, rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w (REVERSE [0w; 0x1fw; 0xffw]) = (8191w : bytes32)` by
    (simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
          byteTheory.byte_index_def, byteTheory.word_slice_alt_zero,
          byteTheory.word_slice_alt_shift, byteTheory.word_slice_alt_empty]) >>
  simp[vfmDecreasesGasTheory.run_eq_tr] >>
  ntac 5 (simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_call_data_load_def,
    step_swap_def, step_binop_def, get_call_data_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def, CONJUNCT1 byteTheory.word_of_bytes_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse])
QED

Theorem beacon_roots_dispatch_run[local]:
  s.contexts = (c, rb)::cs /\ c.pc = 0 /\ c.stack = [] /\
  c.jumpDest = NONE /\ c.gasUsed + 21 <= c.msgParams.gasLimit /\
  c.msgParams.code = beacon_roots_code /\
  c.msgParams.parsed = parse_code 0 FEMPTY beacon_roots_code /\
  c.msgParams.caller = system_address ==>
  run s = run (s with contexts :=
    (c with <|pc := 77; gasUsed := c.gasUsed + 21|>, rb)::cs)
Proof
  strip_tac >>
  irule (system_privileged_dispatch_run |> SPEC_ALL |> Q.INST
    [`dest` |-> `0x4dw:byte`,
     `caller_bytes` |-> `TAKE 20 (DROP 2 beacon_roots_code)`]
    |> SIMP_RULE (srw_ss()) []) >>
  simp[GSYM beacon_roots_instruction_def, beacon_roots_parse,
       GSYM beacon_roots_caller_word_def, beacon_roots_caller_word] >>
  simp[beacon_roots_code_def]
QED

Theorem beacon_roots_not_delegation[local]:
  get_delegate beacon_roots_code = NONE
Proof
  EVAL_TAC
QED

(* Header bounds exclude truncation by TIMESTAMP/NUMBER. Queue bounds exclude
   wrapped head subtraction and excess addition; storage keys may still wrap.
   Canonical system paths leave account code, nonce and balance unchanged. *)

Theorem beacon_roots_run_certificate[local]:
  blk.timeStamp < 2 ** 256 ==>
  let tx = <|from := system_address; to := SOME beacon_roots_address;
    data := word_to_bytes blk.parentBeaconBlockRoot T; nonce := 0; value := 0;
    gasLimit := system_transaction_gas; gasPrice := blk.baseFeePerGas;
    accessList := []; blobVersionedHashes := []; maxFeePerBlobGas := NONE;
    maxFeePerGas := NONE; authorizationList := []|> in
  let rb = initial_rollback accounts <|addresses := fEMPTY; storageKeys := fEMPTY|> in
  let s0 = <|contexts := [(initial_context beacon_roots_address beacon_roots_code F
                           empty_return_destination tx, rb)];
    txParams := initial_tx_params chainId prevHashes blk tx 0;
    rollback := rb; originalAccounts := accounts;
    msdomain := Collect (d with addresses updated_by fINSERT beacon_roots_address)|> in
  ?s c rb' d'. run s0 = SOME (INR NONE, s) /\ s.contexts = [(c, rb')] /\
    c.returnData = [] /\ s.rollback.accounts = update_beacon_block [] blk accounts /\
    s.rollback.toDelete = [] /\ s.msdomain = Collect d'
Proof
  strip_tac >> simp_tac (srw_ss()) [LET_THM] >>
  qmatch_goalsub_abbrev_tac `run s0` >>
  qabbrev_tac `c0 = FST (HD s0.contexts)` >>
  qabbrev_tac `rb0 = SND (HD s0.contexts)` >>
  `run s0 = run (s0 with contexts :=
      [(c0 with <|pc := 77; gasUsed := c0.gasUsed + 21|>, rb0)])` by
    (irule beacon_roots_dispatch_run >>
     simp[Abbr `c0`, Abbr `rb0`, Abbr `s0`,
          vfmContextTheory.initial_context_def,
          vfmContextTheory.initial_msg_params_def,
          system_transaction_gas_def]) >>
  asm_rewrite_tac [] >>
  qabbrev_tac `c77 = c0 with <|pc := 77; gasUsed := c0.gasUsed + 21|>` >>
  `run (s0 with contexts := [(c77, rb0)]) =
   run (s0 with contexts :=
     [(c77 with <|pc := c77.pc + 1; gasUsed := c77.gasUsed + 1|>, rb0)])` by
    (irule system_jumpdest_run >>
     simp[Abbr `c77`, Abbr `c0`, Abbr `s0`,
          vfmContextTheory.initial_context_def,
          vfmContextTheory.initial_msg_params_def,
          system_transaction_gas_def, GSYM beacon_roots_instruction_def,
          beacon_roots_parse]) >>
  asm_rewrite_tac [] >>
  qabbrev_tac `c78 = c77 with <|pc := c77.pc + 1; gasUsed := c77.gasUsed + 1|>` >>
  `run (s0 with contexts := [(c78, rb0)]) =
   run (s0 with contexts := [(c78 with <|pc := 86; gasUsed := c78.gasUsed + 15;
     stack := [with_zero word_mod (n2w s0.txParams.blockTimeStamp) 8191w;
               n2w s0.txParams.blockTimeStamp;
               with_zero word_mod (n2w s0.txParams.blockTimeStamp) 8191w]|>, rb0)])` by
    (irule beacon_roots_index_run >>
     simp[Abbr `c78`, Abbr `c77`, Abbr `c0`, Abbr `s0`,
          vfmContextTheory.initial_context_def,
          vfmContextTheory.initial_msg_params_def, system_transaction_gas_def]) >>
  asm_rewrite_tac [] >>
  qabbrev_tac `c86 = c78 with <|pc := 86; gasUsed := c78.gasUsed + 15;
     stack := [with_zero word_mod (n2w s0.txParams.blockTimeStamp) 8191w;
               n2w s0.txParams.blockTimeStamp;
               with_zero word_mod (n2w s0.txParams.blockTimeStamp) 8191w]|>` >>
  qabbrev_tac `key = with_zero word_mod (n2w s0.txParams.blockTimeStamp) 8191w : bytes32` >>
  qabbrev_tac `value = n2w s0.txParams.blockTimeStamp : bytes32` >>
  qabbrev_tac `cur = lookup_storage key
    (lookup_account beacon_roots_address accounts).storage` >>
  qabbrev_tac `cost = sstore_base_gas cur cur value + zero_warm cold_sload_cost` >>
  Cases_on `sstore_refund_updates cur cur value` >>
  rename1 `sstore_refund_updates cur cur value = (ad, su)` >>
  qabbrev_tac `s87 = s0 with <|
    contexts := [(c86 with <|pc := c86.pc + 1; stack := [key];
      gasUsed := c86.gasUsed + cost; addRefund := ad + c86.addRefund;
      subRefund := su + c86.subRefund|>, rb0)];
    rollback := s0.rollback with <|
      accounts := update_account beacon_roots_address
        ((lookup_account beacon_roots_address s0.rollback.accounts) with
          storage updated_by update_storage key value) s0.rollback.accounts;
      accesses := s0.rollback.accesses with storageKeys updated_by
        fINSERT (SK beacon_roots_address key)|>;
    msdomain := Collect ((d with addresses updated_by fINSERT beacon_roots_address)
      with storageKeys updated_by fINSERT (SK beacon_roots_address key))|>` >>
  `run (s0 with contexts := [(c86, rb0)]) = run s87` by
    (simp_tac pure_ss [Abbr `s87`] >> irule system_sstore_run >>
     rpt (qpat_x_assum `run _ = _` kall_tac) >>
     qpat_x_assum `Abbrev (rb0 = _)` kall_tac >>
     simp[Abbr `c86`, Abbr `c78`, Abbr `c77`, Abbr `c0`, Abbr `s0`,
          vfmContextTheory.initial_context_def,
          vfmContextTheory.initial_msg_params_def,
          vfmContextTheory.initial_rollback_def,
          GSYM beacon_roots_instruction_def, beacon_roots_parse,
          system_transaction_gas_def, call_stipend_def] >>
     simp[Abbr `cost`, Abbr `cur`, zero_warm_def, sstore_base_gas_def,
          warm_access_cost_def, cold_sload_cost_def,
          storage_set_cost_def, storage_update_cost_def] >>
     rpt IF_CASES_TAC >> simp[]) >>
  asm_rewrite_tac [] >>
  qabbrev_tac `c87 = FST (HD s87.contexts)` >>
  qabbrev_tac `c95 = c87 with <|pc := 95; gasUsed := c87.gasUsed + 14;
    stack := [8191w + key; word_of_bytes F 0w
      (REVERSE (take_pad_0 32 (buffer_to_list c87.msgParams.data)))]|>` >>
  `run s87 = run (s87 with contexts := [(c95, rb0)])` by
    (simp_tac pure_ss [Abbr `c95`] >>
     `s87 = s87 with contexts := [(c87, rb0)]` by
       simp[Abbr `c87`, Abbr `s87`] >>
     pop_assum (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     irule beacon_roots_data_run >>
     rpt (qpat_x_assum `run _ = _` kall_tac) >>
     simp[Abbr `c87`, Abbr `s87`, Abbr `c86`, Abbr `c78`, Abbr `c77`,
       Abbr `c0`, Abbr `s0`, vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def, system_transaction_gas_def] >>
     simp[Abbr `cost`, zero_warm_def, sstore_base_gas_def,
       warm_access_cost_def, cold_sload_cost_def,
       storage_set_cost_def, storage_update_cost_def] >>
     rpt IF_CASES_TAC >> simp[]) >>
  asm_rewrite_tac [] >>
  qabbrev_tac `key2 = 8191w + key : bytes32` >>
  qabbrev_tac `root = word_of_bytes F 0w
    (REVERSE (take_pad_0 32 (buffer_to_list c87.msgParams.data))) : bytes32` >>
  qabbrev_tac `cur2 = lookup_storage key2
    (lookup_account beacon_roots_address s87.rollback.accounts).storage` >>
  qabbrev_tac `orig2 = lookup_storage key2
    (lookup_account beacon_roots_address s87.originalAccounts).storage` >>
  qabbrev_tac `cost2 = sstore_base_gas orig2 cur2 root + zero_warm
    (if fIN (SK beacon_roots_address key2) s87.rollback.accesses.storageKeys
     then warm_access_cost else cold_sload_cost)` >>
  Cases_on `sstore_refund_updates orig2 cur2 root` >>
  rename1 `sstore_refund_updates orig2 cur2 root = (ad2, su2)` >>
  qabbrev_tac `s96 = s87 with <|
    contexts := [(c95 with <|pc := c95.pc + 1; stack := [];
      gasUsed := c95.gasUsed + cost2; addRefund := ad2 + c95.addRefund;
      subRefund := su2 + c95.subRefund|>, rb0)];
    rollback := s87.rollback with <|
      accounts := update_account beacon_roots_address
        ((lookup_account beacon_roots_address s87.rollback.accounts) with
          storage updated_by update_storage key2 root) s87.rollback.accounts;
      accesses := s87.rollback.accesses with storageKeys updated_by
        fINSERT (SK beacon_roots_address key2)|>;
    msdomain := Collect (((d with addresses updated_by fINSERT beacon_roots_address)
      with storageKeys updated_by fINSERT (SK beacon_roots_address key))
      with storageKeys updated_by fINSERT (SK beacon_roots_address key2))|>` >>
  `run (s87 with contexts := [(c95, rb0)]) = run s96` by
    (simp_tac pure_ss [Abbr `s96`] >> irule system_sstore_run >>
     simp[Abbr `cost2`, Abbr `cur2`, Abbr `orig2`] >>
     rpt (qpat_x_assum `run _ = _` kall_tac) >>
     rpt (qpat_x_assum `sstore_refund_updates _ _ _ = _` kall_tac) >>
     qpat_x_assum `Abbrev (rb0 = _)` kall_tac >>
     simp[Abbr `c95`, Abbr `key2`, Abbr `root`, Abbr `c87`, Abbr `s87`,
       Abbr `c86`, Abbr `c78`, Abbr `c77`, Abbr `c0`, Abbr `s0`,
       vfmContextTheory.initial_context_def, vfmContextTheory.initial_msg_params_def,
       GSYM beacon_roots_instruction_def, beacon_roots_parse,
       system_transaction_gas_def, call_stipend_def] >>
     simp[Abbr `cost`, zero_warm_def, sstore_base_gas_def,
       warm_access_cost_def, cold_sload_cost_def,
       storage_set_cost_def, storage_update_cost_def] >>
     rpt IF_CASES_TAC >> simp[]) >>
  asm_rewrite_tac [] >>
  rpt (qpat_x_assum `run _ = _` kall_tac) >>
  qabbrev_tac `cf = FST (HD s96.contexts)` >>
  `run s96 = SOME (INR NONE, s96 with contexts :=
    [(cf with returnData := [], rb0)])` by
    (`s96 = s96 with contexts := [(cf, rb0)]` by
       simp[Abbr `cf`, Abbr `s96`] >>
     pop_assum (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     irule system_stop_run >>
     simp[Abbr `cf`, Abbr `s96`, Abbr `c95`, Abbr `c87`, Abbr `s87`,
       Abbr `c86`, Abbr `c78`, Abbr `c77`, Abbr `c0`, Abbr `s0`,
       vfmContextTheory.initial_context_def, vfmContextTheory.initial_msg_params_def,
       GSYM beacon_roots_instruction_def, beacon_roots_parse]) >>
  asm_rewrite_tac [] >>
  simp[] >>
  qpat_x_assum `run _ = _` kall_tac >>
  rpt (qpat_x_assum `sstore_refund_updates _ _ _ = _` kall_tac) >>
  map_every (fn v => qpat_x_assum v kall_tac)
    [`Abbrev (cf = _)`, `Abbrev (c95 = _)`, `Abbrev (cur2 = _)`,
     `Abbrev (orig2 = _)`, `Abbrev (cost2 = _)`, `Abbrev (cost = _)`,
     `Abbrev (cur = _)`, `Abbrev (rb0 = _)`] >>
  simp[Abbr `s96`, Abbr `s87`, Abbr `s0`,
    vfmContextTheory.initial_rollback_def, update_beacon_block_def,
    update_history_block_def] >>
  simp[Abbr `root`, Abbr `c87`, Abbr `c86`, Abbr `c78`, Abbr `c77`, Abbr `c0`,
    vfmContextTheory.initial_context_def, vfmContextTheory.initial_msg_params_def,
    vfmContextTheory.initial_tx_params_def] >>
  simp[Abbr `key2`, Abbr `key`, Abbr `value`,
    vfmContextTheory.initial_tx_params_def, with_zero_def, wordsTheory.word_mod_def,
    take_pad_0_def, byteTheory.LENGTH_word_to_bytes,
    vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def] >>
  `blk.timeStamp MOD 115792089237316195423570985008687907853269984665640564039457584007913129639936 = blk.timeStamp` by
    (irule arithmeticTheory.LESS_MOD >> fs[]) >>
  simp[listTheory.TAKE_LENGTH_ID_rwt, listTheory.PAD_RIGHT,
    byteTheory.LENGTH_word_to_bytes, GSYM wordsTheory.word_add_n2w] >>
  rewrite_tac[GSYM byteTheory.word_to_bytes_be_def,
    cv_stdTheory.word_to_bytes_be_eq_bytes_of_num, listTheory.REVERSE_REVERSE,
    GSYM cv_stdTheory.word_to_bytes_le_eq_bytes_of_num,
    byteTheory.word_to_bytes_le_def] >>
  simp[] >>
  Cases_on `accounts beacon_roots_address` >>
  simp[vfmStateTheory.recordtype_account_state_seldef_storage_fupd_def]
QED

Theorem beacon_roots_code_correspondence:
  (lookup_account beacon_roots_address accounts).code = beacon_roots_code ∧
  blk.timeStamp < 2 ** 256 ⇒
  ∃d'. run_system_transaction F (Collect d) chainId prevHashes blk accounts
         beacon_roots_address (word_to_bytes blk.parentBeaconBlockRoot T) =
       SOME ([], update_beacon_block [] blk accounts, Collect d')
Proof
  rpt strip_tac >> drule beacon_roots_run_certificate >>
  disch_then (qspecl_then [`prevHashes`, `d`, `chainId`, `accounts`] mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  simp[run_system_transaction_def, vfmContextTheory.code_from_tx_def,
       beacon_roots_not_delegation, domain_check_def, bind_def,
       ignore_bind_def, return_def, set_domain_def, vfm_abort_def,
       process_deletions_def] >>
  metis_tac[]
QED

Definition history_storage_instruction_def:
  history_storage_instruction pc =
    FLOOKUP (parse_code 0 FEMPTY history_storage_code) pc
End
val () = cv_auto_trans history_storage_instruction_def;

Theorem history_storage_parse[local]:
  history_storage_instruction 0 = SOME Caller /\
  history_storage_instruction 1 = SOME (Push 20 (TAKE 20 (DROP 2 history_storage_code))) /\
  history_storage_instruction 22 = SOME Eq /\
  history_storage_instruction 23 = SOME (Push 1 [0x46w]) /\
  history_storage_instruction 25 = SOME JumpI /\
  history_storage_instruction 70 = SOME JumpDest /\
  history_storage_instruction 71 = SOME (Push 0 []) /\
  history_storage_instruction 72 = SOME CallDataLoad /\
  history_storage_instruction 73 = SOME (Push 2 [0x1fw; 0xffw]) /\
  history_storage_instruction 76 = SOME (Push 1 [1w]) /\
  history_storage_instruction 78 = SOME Number /\
  history_storage_instruction 79 = SOME Sub /\
  history_storage_instruction 80 = SOME Mod /\
  history_storage_instruction 81 = SOME SStore /\
  history_storage_instruction 82 = SOME Stop
Proof
  rpt conj_tac >> CONV_TAC cv_eval
QED

Definition history_storage_caller_word_def:
  history_storage_caller_word : bytes32 =
    word_of_bytes F 0w (REVERSE (TAKE 20 (DROP 2 history_storage_code)))
End
val () = cv_auto_trans (REWRITE_RULE [GSYM byteTheory.word_of_bytes_le_def]
  history_storage_caller_word_def);

Theorem history_storage_caller_word[local]:
  history_storage_caller_word = (w2w system_address : bytes32)
Proof
  CONV_TAC cv_eval
QED

Theorem history_storage_dispatch_run[local]:
  s.contexts = (c, rb)::cs /\ c.pc = 0 /\ c.stack = [] /\
  c.jumpDest = NONE /\ c.gasUsed + 21 <= c.msgParams.gasLimit /\
  c.msgParams.code = history_storage_code /\
  c.msgParams.parsed = parse_code 0 FEMPTY history_storage_code /\
  c.msgParams.caller = system_address ==>
  run s = run (s with contexts :=
    (c with <|pc := 70; gasUsed := c.gasUsed + 21|>, rb)::cs)
Proof
  strip_tac >>
  irule (system_privileged_dispatch_run |> SPEC_ALL |> Q.INST
    [`dest` |-> `0x46w:byte`,
     `caller_bytes` |-> `TAKE 20 (DROP 2 history_storage_code)`]
    |> SIMP_RULE (srw_ss()) []) >>
  simp[GSYM history_storage_instruction_def, history_storage_parse,
       GSYM history_storage_caller_word_def, history_storage_caller_word] >>
  simp[history_storage_code_def]
QED

Theorem history_storage_body_run[local]:
  c.pc = 71 /\ c.stack = [] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY history_storage_code /\
  c.gasUsed + 21 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) =
  run (s with contexts :=
    (c with <|pc := 81; gasUsed := c.gasUsed + 21;
      stack := [with_zero word_mod (n2w s.txParams.blockNumber - 1w) 8191w;
        word_of_bytes F 0w (REVERSE (take_pad_0 32 (buffer_to_list c.msgParams.data)))]|>, rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w (REVERSE [0x1fw; 0xffw]) = (8191w : bytes32)` by
    (simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
          byteTheory.byte_index_def, byteTheory.word_slice_alt_zero,
          byteTheory.word_slice_alt_shift, byteTheory.word_slice_alt_empty]) >>
  `word_of_bytes F 0w [1w] = (1w : bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[vfmDecreasesGasTheory.run_eq_tr] >>
  ntac 4 (simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_call_data_load_def,
    step_txParams_def, step_binop_def, get_call_data_def, get_tx_params_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def, CONJUNCT1 byteTheory.word_of_bytes_def,
    GSYM history_storage_instruction_def, history_storage_parse]) >>
  ntac 3 (simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_txParams_def, step_binop_def, get_tx_params_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def,
    GSYM history_storage_instruction_def, history_storage_parse])
QED

Theorem history_storage_not_delegation[local]:
  get_delegate history_storage_code = NONE
Proof
  EVAL_TAC
QED

Theorem history_storage_run_certificate[local]:
  0 < blk.number /\ blk.number < 2 ** 256 ==>
  let tx = <|from := system_address; to := SOME history_storage_address;
    data := word_to_bytes parent_hash T; nonce := 0; value := 0;
    gasLimit := system_transaction_gas; gasPrice := blk.baseFeePerGas;
    accessList := []; blobVersionedHashes := []; maxFeePerBlobGas := NONE;
    maxFeePerGas := NONE; authorizationList := []|> in
  let rb = initial_rollback accounts <|addresses := fEMPTY; storageKeys := fEMPTY|> in
  let s0 = <|contexts := [(initial_context history_storage_address history_storage_code F
                           empty_return_destination tx, rb)];
    txParams := initial_tx_params chainId prevHashes blk tx 0;
    rollback := rb; originalAccounts := accounts;
    msdomain := Collect (d with addresses updated_by fINSERT history_storage_address)|> in
  ?s c rb' d'. run s0 = SOME (INR NONE, s) /\ s.contexts = [(c, rb')] /\
    c.returnData = [] /\ s.rollback.accounts = update_history_block [parent_hash] blk accounts /\
    s.rollback.toDelete = [] /\ s.msdomain = Collect d'
Proof
  strip_tac >> simp_tac (srw_ss()) [LET_THM] >>
  qmatch_goalsub_abbrev_tac `run s0` >>
  qabbrev_tac `c0 = FST (HD s0.contexts)` >>
  qabbrev_tac `rb0 = SND (HD s0.contexts)` >>
  `run s0 = run (s0 with contexts :=
      [(c0 with <|pc := 70; gasUsed := c0.gasUsed + 21|>, rb0)])` by
    (irule history_storage_dispatch_run >>
     simp[Abbr `c0`, Abbr `rb0`, Abbr `s0`,
          vfmContextTheory.initial_context_def,
          vfmContextTheory.initial_msg_params_def,
          system_transaction_gas_def]) >>
  asm_rewrite_tac [] >>
  qabbrev_tac `c70 = c0 with <|pc := 70; gasUsed := c0.gasUsed + 21|>` >>
  `run (s0 with contexts := [(c70, rb0)]) =
   run (s0 with contexts :=
     [(c70 with <|pc := c70.pc + 1; gasUsed := c70.gasUsed + 1|>, rb0)])` by
    (irule system_jumpdest_run >>
     simp[Abbr `c70`, Abbr `c0`, Abbr `s0`,
          vfmContextTheory.initial_context_def,
          vfmContextTheory.initial_msg_params_def,
          system_transaction_gas_def, GSYM history_storage_instruction_def,
          history_storage_parse]) >>
  asm_rewrite_tac [] >>
  qabbrev_tac `c71 = c70 with <|pc := c70.pc + 1; gasUsed := c70.gasUsed + 1|>` >>
  `run (s0 with contexts := [(c71, rb0)]) =
   run (s0 with contexts := [(c71 with <|pc := 81; gasUsed := c71.gasUsed + 21;
     stack := [with_zero word_mod (n2w s0.txParams.blockNumber - 1w) 8191w;
       word_of_bytes F 0w (REVERSE (take_pad_0 32 (buffer_to_list c71.msgParams.data)))]|>, rb0)])` by
    (irule history_storage_body_run >>
     simp[Abbr `c71`, Abbr `c70`, Abbr `c0`, Abbr `s0`,
          vfmContextTheory.initial_context_def,
          vfmContextTheory.initial_msg_params_def, system_transaction_gas_def]) >>
  asm_rewrite_tac [] >>
  qabbrev_tac `key = with_zero word_mod (n2w s0.txParams.blockNumber - 1w) 8191w : bytes32` >>
  qabbrev_tac `root = word_of_bytes F 0w
    (REVERSE (take_pad_0 32 (buffer_to_list c71.msgParams.data))) : bytes32` >>
  qabbrev_tac `c81 = c71 with <|pc := 81; gasUsed := c71.gasUsed + 21;
    stack := [key; root]|>` >>
  qabbrev_tac `cur = lookup_storage key
    (lookup_account history_storage_address accounts).storage` >>
  qabbrev_tac `cost = sstore_base_gas cur cur root + zero_warm cold_sload_cost` >>
  Cases_on `sstore_refund_updates cur cur root` >>
  rename1 `sstore_refund_updates cur cur root = (ad, su)` >>
  qabbrev_tac `s82 = s0 with <|
    contexts := [(c81 with <|pc := c81.pc + 1; stack := [];
      gasUsed := c81.gasUsed + cost; addRefund := ad + c81.addRefund;
      subRefund := su + c81.subRefund|>, rb0)];
    rollback := s0.rollback with <|
      accounts := update_account history_storage_address
        ((lookup_account history_storage_address s0.rollback.accounts) with
          storage updated_by update_storage key root) s0.rollback.accounts;
      accesses := s0.rollback.accesses with storageKeys updated_by
        fINSERT (SK history_storage_address key)|>;
    msdomain := Collect ((d with addresses updated_by fINSERT history_storage_address)
      with storageKeys updated_by fINSERT (SK history_storage_address key))|>` >>
  `run (s0 with contexts := [(c81, rb0)]) = run s82` by
    (simp_tac pure_ss [Abbr `s82`] >> irule system_sstore_run >>
     rpt (qpat_x_assum `run _ = _` kall_tac) >>
     qpat_x_assum `Abbrev (rb0 = _)` kall_tac >>
     simp[Abbr `c81`, Abbr `c71`, Abbr `c70`,
       Abbr `c0`, Abbr `s0`, vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def, vfmContextTheory.initial_rollback_def,
       GSYM history_storage_instruction_def, history_storage_parse,
       system_transaction_gas_def, call_stipend_def] >>
     simp[Abbr `cost`, Abbr `cur`, zero_warm_def, sstore_base_gas_def,
       warm_access_cost_def, cold_sload_cost_def,
       storage_set_cost_def, storage_update_cost_def] >>
     rpt IF_CASES_TAC >> simp[]) >>
  asm_rewrite_tac [] >>
  rpt (qpat_x_assum `run _ = _` kall_tac) >>
  qabbrev_tac `cf = FST (HD s82.contexts)` >>
  `run s82 = SOME (INR NONE, s82 with contexts :=
    [(cf with returnData := [], rb0)])` by
    (`s82 = s82 with contexts := [(cf, rb0)]` by
       simp[Abbr `cf`, Abbr `s82`] >>
     pop_assum (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     irule system_stop_run >>
     simp[Abbr `cf`, Abbr `s82`, Abbr `c81`, Abbr `c71`, Abbr `c70`,
       Abbr `c0`, Abbr `s0`, vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def,
       GSYM history_storage_instruction_def, history_storage_parse]) >>
  asm_rewrite_tac [] >> simp[] >>
  qpat_x_assum `run _ = _` kall_tac >>
  rpt (qpat_x_assum `sstore_refund_updates _ _ _ = _` kall_tac) >>
  map_every (fn v => qpat_x_assum v kall_tac)
    [`Abbrev (cf = _)`, `Abbrev (cost = _)`, `Abbrev (cur = _)`,
     `Abbrev (c81 = _)`, `Abbrev (rb0 = _)`] >>
  simp[Abbr `s82`, Abbr `s0`, vfmContextTheory.initial_rollback_def,
    update_history_block_def] >>
  simp[Abbr `root`, Abbr `c71`, Abbr `c70`, Abbr `c0`, Abbr `key`,
    vfmContextTheory.initial_context_def, vfmContextTheory.initial_msg_params_def,
    vfmContextTheory.initial_tx_params_def, take_pad_0_def,
    listTheory.TAKE_LENGTH_ID_rwt, listTheory.PAD_RIGHT,
    byteTheory.LENGTH_word_to_bytes] >>
  rewrite_tac[GSYM byteTheory.word_to_bytes_be_def,
    cv_stdTheory.word_to_bytes_be_eq_bytes_of_num, listTheory.REVERSE_REVERSE,
    GSYM cv_stdTheory.word_to_bytes_le_eq_bytes_of_num,
    byteTheory.word_to_bytes_le_def] >>
  simp[] >>
  `((n2w blk.number : bytes32) - 1w) = n2w (blk.number - 1)` by
    (sym_tac >> irule wordsTheory.n2w_sub >> simp[]) >>
  `blk.number - 1 < 2 ** 256` by decide_tac >>
  simp[with_zero_def, wordsTheory.word_mod_def, wordsTheory.w2n_n2w,
    wordsTheory.dimword_def] >>
  Cases_on `lookup_account history_storage_address accounts` >>
  simp[vfmStateTheory.recordtype_account_state_seldef_storage_fupd_def] >> gvs[]
QED

Theorem history_storage_code_correspondence:
  (lookup_account history_storage_address accounts).code = history_storage_code ∧
  0 < blk.number ∧ blk.number < 2 ** 256 ⇒
  ∃d'. run_system_transaction F (Collect d) chainId prevHashes blk accounts
         history_storage_address (word_to_bytes parent_hash T) =
       SOME ([], update_history_block [parent_hash] blk accounts, Collect d')
Proof
  rpt strip_tac >>
  drule_all history_storage_run_certificate >>
  disch_then (qspecl_then [`prevHashes`, `parent_hash`, `d`, `chainId`, `accounts`] mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  simp[run_system_transaction_def, vfmContextTheory.code_from_tx_def,
       history_storage_not_delegation, domain_check_def, bind_def,
       ignore_bind_def, return_def, set_domain_def, vfm_abort_def,
       process_deletions_def] >>
  metis_tac[]
QED

Theorem read_withdrawal_request_length[local]:
  LENGTH (read_withdrawal_request storage idx) = 76
Proof
  simp[read_withdrawal_request_def, byteTheory.LENGTH_word_to_bytes]
QED

Theorem read_consolidation_request_length[local]:
  LENGTH (read_consolidation_request storage idx) = 116
Proof
  simp[read_consolidation_request_def, byteTheory.LENGTH_word_to_bytes]
QED

Theorem queue_sender_bytes[local]:
  TAKE 20 (word_to_bytes ((w:bytes32) << 96) T) =
  DROP 12 (word_to_bytes w T)
Proof
  simp[byteTheory.word_to_bytes_def] >>
  irule listTheory.LIST_EQ >>
  simp[byteTheory.LENGTH_word_to_bytes_aux, listTheory.EL_TAKE,
    listTheory.EL_DROP, byteTheory.EL_word_to_bytes_aux] >>
  rpt strip_tac >>
  simp[byteTheory.get_byte_def, byteTheory.byte_index_def] >>
  simp[wordsTheory.w2w, wordsTheory.word_lsr_def, wordsTheory.word_lsl_def,
    fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >> simp[] >>
  `i + 8 * (31 - x) - 96 = i + 8 * (19 - x)` by decide_tac >> simp[]
QED

Theorem queue_read_el[local]:
  i < sz ==>
  EL i (buffer_read off sz b) =
    if off + i < buffer_length b then EL (off + i) (buffer_to_list b)
    else 0w
Proof
  rw[vfmBufferTheory.buffer_read_to_list, take_pad_0_def,
     listTheory.PAD_RIGHT, listTheory.EL_APPEND_EQN,
     listTheory.EL_TAKE, listTheory.EL_DROP, rich_listTheory.EL_REPLICATE,
     listTheory.LENGTH_TAKE_EQ, vfmBufferTheory.LENGTH_buffer_to_list]
  >> gvs[]
QED

Theorem queue_read_extend[local]:
  buffer_read off sz (buffer_extend n b) = buffer_read off sz b
Proof
  irule listTheory.LIST_EQ
  >> simp[vfmBufferTheory.buffer_read_to_list]
  >> rpt strip_tac
  >> simp[GSYM vfmBufferTheory.buffer_read_to_list, queue_read_el,
          vfmBufferTheory.buffer_to_list_extend,
          vfmBufferTheory.buffer_length_extend,
          vfmBufferTheory.LENGTH_buffer_to_list,
          listTheory.EL_APPEND_EQN, rich_listTheory.EL_REPLICATE]
  >> rw[] >> gvs[]
QED

Theorem queue_read_write_el[local]:
  i < sz ==>
  EL i (buffer_read off sz (buffer_write p bs b)) =
    if p <= off + i /\ off + i < p + LENGTH bs
    then EL (off + i - p) bs else EL i (buffer_read off sz b)
Proof
  Cases_on `bs = []` >- simp[]
  >> strip_tac
  >> simp[queue_read_el, vfmBufferTheory.buffer_to_list_write,
          vfmBufferTheory.buffer_length_write]
  >> rw[listTheory.EL_APPEND_EQN, listTheory.EL_TAKE,
        listTheory.PAD_RIGHT, listTheory.LENGTH_TAKE_EQ,
        vfmBufferTheory.LENGTH_buffer_to_list,
        rich_listTheory.EL_REPLICATE, listTheory.EL_DROP,
        arithmeticTheory.MAX_DEF]
  >> gvs[]
QED

Theorem queue_read_write_cong[local]:
  (!off sz. buffer_read off sz b = buffer_read off sz b') ==>
  buffer_read off sz (buffer_write p bs b) =
  buffer_read off sz (buffer_write p bs b')
Proof
  strip_tac
  >> irule listTheory.LIST_EQ
  >> simp[vfmBufferTheory.buffer_read_to_list]
  >> rpt strip_tac
  >> simp[GSYM vfmBufferTheory.buffer_read_to_list, queue_read_write_el]
QED

Theorem queue_read_write_extend[local]:
  buffer_read off sz (buffer_write p bs (buffer_extend n b)) =
  buffer_read off sz (buffer_write p bs b)
Proof
  irule queue_read_write_cong >> simp[queue_read_extend]
QED

Theorem queue_take_read[local]:
  off + sz <= buffer_length b ==>
  buffer_take off sz b = buffer_read off sz b
Proof
  strip_tac
  >> simp[vfmBufferTheory.buffer_take_to_list,
          vfmBufferTheory.buffer_read_to_list, take_pad_0_def,
          listTheory.PAD_RIGHT, listTheory.LENGTH_TAKE_EQ,
          vfmBufferTheory.LENGTH_buffer_to_list]
QED

Theorem queue_take_read_cong[local]:
  (!off sz. buffer_read off sz b = buffer_read off sz b') /\
  off + sz <= buffer_length b /\ off + sz <= buffer_length b' ==>
  buffer_take off sz b = buffer_take off sz b'
Proof
  simp[queue_take_read]
QED

Theorem queue_write_prefix[local]:
  off <= buffer_length b /\ n <= LENGTH bs ==>
  buffer_take 0 (off + n) (buffer_write off bs b) =
  buffer_take 0 off b ++ TAKE n bs
Proof
  strip_tac >>
  simp[vfmBufferTheory.buffer_take_to_list, vfmBufferTheory.buffer_to_list_write_le,
    rich_listTheory.TAKE_APPEND, listTheory.LENGTH_TAKE_EQ,
    vfmBufferTheory.LENGTH_buffer_to_list] >>
  `n - LENGTH bs = 0` by decide_tac >>
  simp[listTheory.TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF]
QED

Theorem queue_write_byte_tail[local]:
  0 < n ==>
  buffer_take i n (buffer_write i [a] b) =
  [a] ++ buffer_take (i + 1) (n - 1) b
Proof
  Cases_on `n` >- simp[] >> strip_tac >>
  simp_tac (srw_ss()) [arithmeticTheory.SUC_SUB1] >>
  rewrite_tac[arithmeticTheory.ADD1] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  once_rewrite_tac[vfmBufferTheory.buffer_take_split] >>
  simp[vfmBufferTheory.buffer_take_write_same,
    vfmBufferTheory.buffer_take_write_after]
QED

Theorem consolidation_record_memory[local]:
  off <= buffer_length b ==>
  let base = 4 + idx * 4 in
  let w0 = lookup_storage (n2w base) storage in
  let w1 = lookup_storage (n2w (base + 1)) storage in
  let w2 = lookup_storage (n2w (base + 2)) storage in
  let w3 = lookup_storage (n2w (base + 3)) storage in
  let b1 = buffer_write off (word_to_bytes (w0 << 96) T) b in
  let b2 = buffer_write (off + 20) (word_to_bytes w1 T) b1 in
  let b3 = buffer_write (off + 52) (word_to_bytes w2 T) b2 in
  let b4 = buffer_write (off + 84) (word_to_bytes w3 T) b3 in
  buffer_take 0 (off + 116) b4 = buffer_take 0 off b ++ read_consolidation_request storage idx
Proof
  strip_tac >> simp_tac (srw_ss()) [LET_THM] >>
  `off + 116 = (off + 84) + 32` by decide_tac >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[queue_write_prefix] >>
  `!w:bytes32. word_to_bytes w T <> []` by
    (gen_tac >> pure_once_rewrite_tac[GSYM listTheory.LENGTH_NIL] >>
     pure_rewrite_tac[byteTheory.LENGTH_word_to_bytes] >> simp[]) >>
  simp[byteTheory.LENGTH_word_to_bytes] >>
  `off + 84 = (off + 52) + 32` by decide_tac >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[queue_write_prefix] >>
  simp[byteTheory.LENGTH_word_to_bytes] >>
  `off + 52 = (off + 20) + 32` by decide_tac >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[queue_write_prefix] >>
  simp[byteTheory.LENGTH_word_to_bytes] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[queue_write_prefix] >>
  simp[byteTheory.LENGTH_word_to_bytes, queue_sender_bytes,
    read_consolidation_request_def, listTheory.APPEND_ASSOC,
    listTheory.TAKE_LENGTH_TOO_LONG]
QED

Theorem queue_pubkey_bytes[local]:
  TAKE 16 (word_to_bytes ((w:bytes32) && (-1w << 128)) T) =
  TAKE 16 (word_to_bytes w T)
Proof
  `!j. 128 <= j /\ j < 256 ==> (((-1w:bytes32) << 128) ' j)` by
    (pure_rewrite_tac[wordsTheory.word_lsl_def] >>
     simp[fcpTheory.FCP_BETA, wordsTheory.WORD_NEG_1_T]) >>
  simp[byteTheory.word_to_bytes_def] >>
  irule listTheory.LIST_EQ >>
  simp[byteTheory.LENGTH_word_to_bytes_aux, listTheory.EL_TAKE,
    byteTheory.EL_word_to_bytes_aux] >>
  rpt strip_tac >>
  simp[byteTheory.get_byte_def, byteTheory.byte_index_def] >>
  simp[wordsTheory.w2w, wordsTheory.word_lsr_def, wordsTheory.word_lsl_def,
    wordsTheory.word_and_def, fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >> simp[] >>
  gvs[]
QED

Theorem queue_amount_bytes[local]:
  (GENLIST (\i. (w2w ((w:bytes32) >>> (64 + 8 * i)) : byte)) 8) =
  REVERSE (TAKE 8 (DROP 16 (word_to_bytes w T)))
Proof
  irule listTheory.LIST_EQ >>
  simp[byteTheory.word_to_bytes_def, byteTheory.LENGTH_word_to_bytes_aux,
    listTheory.EL_REVERSE, listTheory.EL_TAKE, listTheory.EL_DROP,
    byteTheory.EL_word_to_bytes_aux] >>
  rpt strip_tac >>
  simp[byteTheory.get_byte_def, byteTheory.byte_index_def] >>
  simp[wordsTheory.w2w, wordsTheory.word_lsr_def,
    fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >> simp[] >>
  `i + (8 * x + 64) = i + 8 * (15 - PRE (8 - x))` by decide_tac >>
  simp[]
QED

Theorem withdrawal_record_memory[local]:
  off <= buffer_length b ==>
  let base = 4 + idx * 3 in
  let w0 = lookup_storage (n2w base) storage in
  let w1 = lookup_storage (n2w (base + 1)) storage in
  let w2 = lookup_storage (n2w (base + 2)) storage in
  let a = w2 >>> 64 in
  let b1 = buffer_write off (word_to_bytes (w0 << 96) T) b in
  let b2 = buffer_write (off + 20) (word_to_bytes w1 T) b1 in
  let b3 = buffer_write (off + 52) (word_to_bytes (w2 && (-1w << 128)) T) b2 in
  let b4 = buffer_write (off + 75) [w2w (a >>> 56)] b3 in
  let b5 = buffer_write (off + 74) [w2w (a >>> 48)] b4 in
  let b6 = buffer_write (off + 73) [w2w (a >>> 40)] b5 in
  let b7 = buffer_write (off + 72) [w2w (a >>> 32)] b6 in
  let b8 = buffer_write (off + 71) [w2w (a >>> 24)] b7 in
  let b9 = buffer_write (off + 70) [w2w (a >>> 16)] b8 in
  let b10 = buffer_write (off + 69) [w2w (a >>> 8)] b9 in
  let b11 = buffer_write (off + 68) [w2w a] b10 in
  buffer_take 0 (off + 76) b11 =
    buffer_take 0 off b ++ read_withdrawal_request storage idx
Proof
  strip_tac >> simp_tac (srw_ss()) [LET_THM] >>
  `!w:bytes32. word_to_bytes w T <> []` by
    (gen_tac >> pure_once_rewrite_tac[GSYM listTheory.LENGTH_NIL] >>
     pure_rewrite_tac[byteTheory.LENGTH_word_to_bytes] >> simp[]) >>
  qmatch_goalsub_abbrev_tac `buffer_write (off + 75) _ m` >>
  `off + 68 <= buffer_length m` by
    simp[Abbr `m`, byteTheory.LENGTH_word_to_bytes] >>
  `off + 76 = (off + 68) + 8` by decide_tac >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  once_rewrite_tac[vfmBufferTheory.buffer_take_split] >>
  simp[vfmBufferTheory.buffer_take_write_before,
    byteTheory.LENGTH_word_to_bytes, queue_write_byte_tail] >>
  `!i b. buffer_take i 0 b = []` by
    simp[vfmBufferTheory.buffer_take_to_list] >>
  simp[] >>
  unabbrev_all_tac >>
  `off + 68 = (off + 52) + 16` by decide_tac >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[queue_write_prefix] >>
  simp[byteTheory.LENGTH_word_to_bytes] >>
  `off + 52 = (off + 20) + 32` by decide_tac >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[queue_write_prefix] >>
  simp[byteTheory.LENGTH_word_to_bytes] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[queue_write_prefix] >>
  simp[byteTheory.LENGTH_word_to_bytes, queue_sender_bytes,
    listTheory.TAKE_LENGTH_TOO_LONG] >>
  simp[read_withdrawal_request_def, SRULE [] queue_pubkey_bytes,
    GSYM queue_amount_bytes, listTheory.APPEND_ASSOC] >>
  CONV_TAC (RAND_CONV (EVAL))
QED

Definition withdrawal_instruction_def:
  withdrawal_instruction pc = FLOOKUP (parse_code 0 FEMPTY withdrawal_request_code) pc
End
val () = cv_auto_trans withdrawal_instruction_def;

Theorem withdrawal_entry_parse[local]:
  withdrawal_instruction 203 = SOME JumpDest /\
  withdrawal_instruction 204 = SOME (Push 1 [3w]) /\
  withdrawal_instruction 206 = SOME SLoad /\
  withdrawal_instruction 207 = SOME (Push 1 [2w]) /\
  withdrawal_instruction 209 = SOME SLoad /\
  withdrawal_instruction 210 = SOME (Dup 0) /\
  withdrawal_instruction 211 = SOME (Dup 2) /\
  withdrawal_instruction 212 = SOME Sub /\
  withdrawal_instruction 213 = SOME (Dup 0) /\
  withdrawal_instruction 214 = SOME (Push 1 [16w]) /\
  withdrawal_instruction 216 = SOME GT /\
  withdrawal_instruction 217 = SOME (Push 1 [223w]) /\
  withdrawal_instruction 219 = SOME JumpI /\
  withdrawal_instruction 220 = SOME Pop /\
  withdrawal_instruction 221 = SOME (Push 1 [16w]) /\
  withdrawal_instruction 223 = SOME JumpDest /\
  withdrawal_instruction 224 = SOME (Push 0 []) /\
  withdrawal_instruction 225 = SOME JumpDest /\
  withdrawal_instruction 226 = SOME (Dup 1) /\
  withdrawal_instruction 227 = SOME (Dup 1) /\
  withdrawal_instruction 228 = SOME Eq /\
  withdrawal_instruction 229 = SOME (Push 2 [1w; 131w]) /\
  withdrawal_instruction 232 = SOME JumpI /\
  withdrawal_instruction 387 = SOME JumpDest
Proof
  rpt conj_tac >> CONV_TAC cv_eval
QED

Theorem system_sload_step[local]:
  c.stack = key::ss /\ c.jumpDest = NONE /\ LENGTH ss < stack_limit /\
  FLOOKUP c.msgParams.parsed c.pc = SOME SLoad /\ s.msdomain = Collect d /\
  address = c.msgParams.callee /\
  cost = (if fIN (SK address key) s.rollback.accesses.storageKeys
          then warm_access_cost else cold_sload_cost) /\
  c.gasUsed + cost <= c.msgParams.gasLimit ==>
  step (s with contexts := (c, rb)::cs) =
    (INL (), s with <|
      contexts := (c with <|pc := c.pc + 1;
        stack := lookup_storage key (lookup_account address s.rollback.accounts).storage :: ss;
        gasUsed := c.gasUsed + cost|>, rb)::cs;
      rollback := s.rollback with accesses :=
        s.rollback.accesses with storageKeys updated_by fINSERT (SK address key);
      msdomain := Collect (d with storageKeys updated_by fINSERT (SK address key))|>)
Proof
  rpt strip_tac >> gvs[] >>
  simp[step_def, step_inst_def, step_sload_def,
    get_callee_def, get_accounts_def, access_slot_def, domain_check_def,
    set_domain_def, consume_gas_def, pop_stack_def, push_stack_def,
    inc_pc_or_jump_def, is_call_def, opcode_def,
    get_current_context_def, set_current_context_def, bind_def,
    ignore_bind_def, return_def, assert_def, handle_def, stack_limit_def] >>
  Cases_on `c` >> Cases_on `s.rollback.accesses` >> Cases_on `s.rollback` >>
  gvs[vfmContextTheory.context_fn_updates,
      vfmContextTheory.rollback_state_fn_updates,
      vfmContextTheory.access_sets_fn_updates]
QED

Theorem system_push_run[local]:
  FLOOKUP c.msgParams.parsed c.pc = SOME (Push n ws) /\
  c.jumpDest = NONE /\ LENGTH c.stack < stack_limit /\
  c.gasUsed + static_gas (Push n ws) <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <| stack := word_of_bytes F 0w (REVERSE ws) :: c.stack;
               gasUsed := c.gasUsed + static_gas (Push n ws);
               pc := c.pc + LENGTH (opcode (Push n ws)) |>, rb)::cs)
Proof
  strip_tac >> irule system_run_step >> irule system_dispatch_push >> simp[]
QED

Theorem system_sload_bounded_run[local]:
  c.stack = key::ss /\ c.jumpDest = NONE /\ LENGTH ss < stack_limit /\
  FLOOKUP c.msgParams.parsed c.pc = SOME SLoad /\ s.msdomain = Collect d /\
  c.gasUsed + 2100 <= c.msgParams.gasLimit ==>
  ?g keys d'. g <= c.gasUsed + 2100 /\
  run (s with contexts := (c, rb)::cs) =
  run (s with <|
    contexts := (c with <|pc := c.pc + 1;
      stack := lookup_storage key (lookup_account c.msgParams.callee s.rollback.accounts).storage :: ss;
      gasUsed := g|>, rb)::cs;
    rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  qabbrev_tac `cost = if fIN (SK c.msgParams.callee key) s.rollback.accesses.storageKeys
    then warm_access_cost else cold_sload_cost` >>
  `cost <= 2100` by
    (simp[Abbr `cost`] >> IF_CASES_TAC >>
     simp[warm_access_cost_def, cold_sload_cost_def]) >>
  qexistsl [`c.gasUsed + cost`,
    `fINSERT (SK c.msgParams.callee key) s.rollback.accesses.storageKeys`,
    `d with storageKeys updated_by fINSERT (SK c.msgParams.callee key)`] >>
  conj_tac >- decide_tac >>
  `c.gasUsed + cost <= c.msgParams.gasLimit` by decide_tac >>
  mp_tac (Q.INST [`address` |-> `c.msgParams.callee`, `cost` |-> `cost`]
    system_sload_step) >>
  (impl_tac >- simp[Abbr `cost`]) >>
  disch_then (mp_tac o MATCH_MP system_run_step) >>
  Cases_on `s.rollback.accesses` >>
  simp[vfmContextTheory.access_sets_fn_updates]
QED

Theorem system_push1_sload_run[local]:
  FLOOKUP c.msgParams.parsed c.pc = SOME (Push 1 [slot]) /\
  FLOOKUP c.msgParams.parsed (c.pc + 2) = SOME SLoad /\
  c.jumpDest = NONE /\ LENGTH c.stack < stack_limit /\
  s.msdomain = Collect d /\ c.gasUsed + 2103 <= c.msgParams.gasLimit ==>
  ?g keys d'. g <= c.gasUsed + 2103 /\
  run (s with contexts := (c, rb)::cs) = run (s with <|
    contexts := (c with <|pc := c.pc + 3;
      stack := lookup_storage (w2w slot) (lookup_account c.msgParams.callee s.rollback.accounts).storage :: c.stack;
      gasUsed := g|>, rb)::cs;
    rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `word_of_bytes F 0w [slot] = (w2w slot:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  qabbrev_tac `c1 = c with <|stack := word_of_bytes F 0w (REVERSE [slot]) :: c.stack;
    gasUsed := c.gasUsed + static_gas (Push 1 [slot]);
    pc := c.pc + LENGTH (opcode (Push 1 [slot]))|>` >>
  `run (s with contexts := (c, rb)::cs) =
   run (s with contexts := (c1, rb)::cs)` by
    (simp_tac pure_ss [Abbr `c1`] >> irule system_push_run >>
     simp[static_gas_def]) >>
  mp_tac (Q.INST [`c` |-> `c1`, `key` |-> `(w2w (slot:byte)):bytes32`,
    `ss` |-> `c.stack`] system_sload_bounded_run) >>
  (impl_tac >- simp[Abbr `c1`, static_gas_def, opcode_def]) >>
  simp[Abbr `c1`, static_gas_def, opcode_def] >>
  strip_tac >> qexistsl [`g`, `keys`, `d'`] >> simp[] >>
  Cases_on `c` >> gvs[vfmContextTheory.context_fn_updates]
QED

Theorem withdrawal_heads_run[local]:
  c.pc = 203 /\ c.stack = [] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  s.msdomain = Collect d /\ c.gasUsed + 4207 <= c.msgParams.gasLimit ==>
  ?g keys d'. g <= c.gasUsed + 4207 /\
  run (s with contexts := (c, rb)::cs) = run (s with <|
    contexts := (c with <|pc := 210;
      stack := [lookup_storage 2w (lookup_account c.msgParams.callee s.rollback.accounts).storage;
                lookup_storage 3w (lookup_account c.msgParams.callee s.rollback.accounts).storage];
      gasUsed := g|>, rb)::cs;
    rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  qabbrev_tac `c1 = c with <|pc := c.pc + 1; gasUsed := c.gasUsed + 1|>` >>
  `run (s with contexts := (c, rb)::cs) =
   run (s with contexts := (c1, rb)::cs)` by
    (simp_tac pure_ss [Abbr `c1`] >> irule system_jumpdest_run >>
     simp[GSYM withdrawal_instruction_def, withdrawal_entry_parse]) >>
  mp_tac (Q.INST [`c` |-> `c1`, `slot` |-> `3w:byte`] system_push1_sload_run) >>
  (impl_tac >- simp[Abbr `c1`, GSYM withdrawal_instruction_def,
    withdrawal_entry_parse, stack_limit_def]) >>
  simp[Abbr `c1`] >>
  disch_then (qx_choose_then `g1` (qx_choose_then `keys1` (qx_choose_then `d1` strip_assume_tac))) >>
  qabbrev_tac `c2 = c with <|pc := 207;
    stack := [lookup_storage 3w (lookup_account c.msgParams.callee s.rollback.accounts).storage];
    gasUsed := g1|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys1; msdomain := Collect d1|>` >>
  mp_tac (Q.INST [`c` |-> `c2`, `s` |-> `s1`, `d` |-> `d1`,
    `slot` |-> `2w:byte`] system_push1_sload_run) >>
  (impl_tac >- simp[Abbr `c2`, Abbr `s1`, GSYM withdrawal_instruction_def,
    withdrawal_entry_parse, stack_limit_def]) >>
  simp[Abbr `c2`, Abbr `s1`] >>
  disch_then (qx_choose_then `g2` (qx_choose_then `keys2` (qx_choose_then `d2` strip_assume_tac))) >>
  qexistsl [`g2`, `keys2`, `d2`] >>
  conj_tac >- decide_tac >>
  simp[]
QED

Theorem system_dup_run[local]:
  FLOOKUP c.msgParams.parsed c.pc = SOME (Dup n) /\ n < 16 /\
  c.jumpDest = NONE /\ n < LENGTH c.stack /\ LENGTH c.stack < stack_limit /\
  c.gasUsed + 3 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := EL n c.stack :: c.stack;
      gasUsed := c.gasUsed + 3; pc := c.pc + 1|>, rb)::cs)
Proof
  strip_tac >> irule system_run_step >>
  simp[step_def, step_inst_def, step_dup_def, consume_gas_def, push_stack_def,
    inc_pc_or_jump_def, is_call_def, opcode_def, static_gas_def,
    get_current_context_def, set_current_context_def, bind_def,
    ignore_bind_def, return_def, assert_def, handle_def, stack_limit_def]
QED

Theorem system_binop_run[local]:
  2 <= LENGTH c.stack /\ c.jumpDest = NONE /\ LENGTH c.stack <= stack_limit /\
  FLOOKUP c.msgParams.parsed c.pc = SOME op /\
  step_inst op = step_binop op f /\ ~is_call op /\ LENGTH (opcode op) = 1 /\
  c.gasUsed + static_gas op <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := f (HD c.stack) (HD (TL c.stack)) :: DROP 2 c.stack;
      gasUsed := c.gasUsed + static_gas op; pc := c.pc + 1|>, rb)::cs)
Proof
  strip_tac >>
  Cases_on `c.stack` >> gvs[] >> Cases_on `t` >> gvs[] >>
  irule system_run_step >>
  simp[step_def, step_binop_def, consume_gas_def, push_stack_def, pop_stack_def,
    inc_pc_or_jump_def, get_current_context_def, set_current_context_def, bind_def,
    ignore_bind_def, return_def, assert_def, handle_def, stack_limit_def]
QED

Theorem system_jumpi_run[local]:
  2 <= LENGTH c.stack /\ c.jumpDest = NONE /\
  FLOOKUP c.msgParams.parsed c.pc = SOME JumpI /\
  (HD (TL c.stack) <> 0w ==>
    FLOOKUP c.msgParams.parsed (w2n (HD c.stack)) = SOME JumpDest /\
    w2n (HD c.stack) < LENGTH c.msgParams.code) /\
  c.gasUsed + 10 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := DROP 2 c.stack; gasUsed := c.gasUsed + 10;
      pc := if HD (TL c.stack) = 0w then c.pc + 1 else w2n (HD c.stack)|>, rb)::cs)
Proof
  strip_tac >> Cases_on `c.stack` >> gvs[] >> Cases_on `t` >> gvs[] >>
  irule system_run_step >> Cases_on `h' = 0w` >>
  simp[step_def, step_inst_def, step_jumpi_def, pop_stack_def,
    consume_gas_def, set_jump_dest_def, inc_pc_or_jump_def, is_call_def,
    static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def] >>
  Cases_on `c` >> gvs[vfmContextTheory.context_fn_updates]
QED

Theorem system_pop_run[local]:
  c.stack <> [] /\ c.jumpDest = NONE /\
  FLOOKUP c.msgParams.parsed c.pc = SOME Pop /\
  c.gasUsed + 2 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := TL c.stack; gasUsed := c.gasUsed + 2;
      pc := c.pc + 1|>, rb)::cs)
Proof
  strip_tac >> Cases_on `c.stack` >> gvs[] >> irule system_run_step >>
  simp[step_def, step_inst_def, step_pop_def, pop_stack_def,
    consume_gas_def, inc_pc_or_jump_def, is_call_def,
    static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def]
QED

Theorem withdrawal_count_test_run[local]:
  c.pc = 210 /\ c.stack = [head; tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  c.gasUsed + 18 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := [b2w (w2n (tail - head) < 16); tail - head; head; tail];
      gasUsed := c.gasUsed + 18; pc := 217|>, rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [16w:byte] = (16w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Sub`, `f` |-> `word_sub:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[16w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `GT`,
    `f` |-> `(\x y:bytes32. b2w (w2n x > w2n y))`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  `-1w * head + tail = tail - head` by wordsLib.WORD_DECIDE_TAC >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac [arithmeticTheory.GREATER_DEF,
    vfmContextTheory.context_fupdcanon] >> REFL_TAC
QED

Theorem withdrawal_count_select_run[local]:
  c.pc = 217 /\ c.stack = [b2w (w2n cnt < 16); cnt; head; tail] /\
  c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  223 < LENGTH c.msgParams.code /\
  c.gasUsed + 21 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := [0w; if w2n cnt < 16 then cnt else 16w; head; tail];
      gasUsed := c.gasUsed + (if w2n cnt < 16 then 16 else 21);
      pc := 225|>, rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [223w:byte] = (223w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  `word_of_bytes F 0w [16w:byte] = (16w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[223w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  Cases_on `w2n cnt < 16` >>
  simp[SimpLHS, system_jumpi_run, b2w_def, wordsTheory.dimword_def,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse] >>
  simp[] >>
  simp[SimpLHS, system_pop_run,
    Q.INST [`n` |-> `1`, `ws` |-> `[16w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, system_jumpdest_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`, `ws` |-> `[]:byte list`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def,
    static_gas_def, opcode_def, byteTheory.word_of_bytes_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_count_run[local]:
  c.pc = 210 /\ c.stack = [head; tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  223 < LENGTH c.msgParams.code /\ w2n head <= w2n tail /\
  c.gasUsed + 39 <= c.msgParams.gasLimit ==>
  ?g. g <= c.gasUsed + 39 /\
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := [0w; n2w (MIN 16 (w2n tail - w2n head)); head; tail];
      gasUsed := g; pc := 225|>, rb)::cs)
Proof
  strip_tac >>
  `w2n (tail - head) = w2n tail - w2n head` by
    (irule wordsTheory.word_sub_w2n >> simp[wordsTheory.WORD_LS]) >>
  qexists_tac `c.gasUsed + 18 + (if w2n (tail - head) < 16 then 16 else 21)` >>
  conj_tac >- (IF_CASES_TAC >> decide_tac) >>
  `c.gasUsed + 18 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all withdrawal_count_test_run >>
  disch_then (fn th => once_rewrite_tac [th]) >>
  mp_tac (Q.INST [`c` |-> `c with <|
    stack := [b2w (w2n (tail - head) < 16); tail - head; head; tail];
    gasUsed := c.gasUsed + 18; pc := 217|>`, `cnt` |-> `tail - head`]
    withdrawal_count_select_run) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => once_rewrite_tac [th]) >>
  `n2w (w2n tail - w2n head) = tail - head` by
    metis_tac[wordsTheory.n2w_w2n] >>
  ` (if w2n (tail - head) < 16 then tail - head else 16w) =
    (n2w (MIN 16 (w2n tail - w2n head)):bytes32)` by
    (Cases_on `w2n (tail - head) < 16` >>
     simp[arithmeticTheory.MIN_DEF]) >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_loop_entry_run[local]:
  c.pc = 203 /\ c.stack = [] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  223 < LENGTH c.msgParams.code /\ s.msdomain = Collect d /\
  head = lookup_storage 2w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  tail = lookup_storage 3w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  w2n head <= w2n tail /\ c.gasUsed + 4246 <= c.msgParams.gasLimit ==>
  ?g keys d'. g <= c.gasUsed + 4246 /\
  run (s with contexts := (c, rb)::cs) = run (s with <|
    contexts := (c with <|pc := 225;
      stack := [0w; n2w (MIN 16 (w2n tail - w2n head)); head; tail];
      gasUsed := g|>, rb)::cs;
    rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `c.gasUsed + 4207 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all withdrawal_heads_run >>
  disch_then (qspecl_then [`rb`, `cs`] strip_assume_tac) >>
  qabbrev_tac `c1 = c with <|pc := 210; stack := [head; tail]; gasUsed := g|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys; msdomain := Collect d'|>` >>
  mp_tac (Q.INST [`c` |-> `c1`, `s` |-> `s1`] withdrawal_count_run) >>
  (impl_tac >- simp[Abbr `c1`]) >>
  disch_then (qx_choose_then `g2` strip_assume_tac) >>
  qexistsl [`g2`, `keys`, `d'`] >>
  conj_tac >- gvs[Abbr `c1`] >>
  gvs[Abbr `c1`, Abbr `s1`]
QED

Theorem withdrawal_copy_address_parse[local]:
  withdrawal_instruction 233 = SOME (Dup 2) /\
  withdrawal_instruction 234 = SOME (Dup 1) /\
  withdrawal_instruction 235 = SOME Add /\
  withdrawal_instruction 236 = SOME (Push 1 [3w]) /\
  withdrawal_instruction 238 = SOME Mul /\
  withdrawal_instruction 239 = SOME (Push 1 [4w]) /\
  withdrawal_instruction 241 = SOME Add /\
  withdrawal_instruction 242 = SOME (Dup 1) /\
  withdrawal_instruction 243 = SOME (Push 1 [76w]) /\
  withdrawal_instruction 245 = SOME Mul /\
  withdrawal_instruction 246 = SOME (Dup 1) /\
  withdrawal_instruction 247 = SOME SLoad
Proof
  rpt conj_tac >> CONV_TAC cv_eval
QED

Theorem withdrawal_loop_test_run[local]:
  c.pc = 225 /\ c.stack = [idx; cnt; head; tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  387 < LENGTH c.msgParams.code /\
  c.gasUsed + 23 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := [idx; cnt; head; tail]; gasUsed := c.gasUsed + 23;
      pc := if idx = cnt then 387 else 233|>, rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [131w:byte; 1w] = (387w:bytes32)` by
    (simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero,
      byteTheory.word_slice_alt_def] >> wordsLib.WORD_DECIDE_TAC) >>
  simp[SimpLHS, system_jumpdest_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Eq`,
    `f` |-> `(\x y:bytes32. b2w (x = y))`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`, `ws` |-> `[1w:byte; 131w]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  Cases_on `idx = cnt` >>
  simp[SimpLHS, system_jumpi_run, b2w_def, wordsTheory.dimword_def,
    GSYM withdrawal_instruction_def, withdrawal_entry_parse] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_push_mask[local]:
  word_of_bytes F 0w (REVERSE (REPLICATE 16 (255w:byte) ++ REPLICATE 16 0w)) =
    ((-1w << 128):bytes32)
Proof
  dep_rewrite.DEP_ONCE_REWRITE_TAC[byteTheory.word_of_bytes_eq_or] >>
  conj_tac >- EVAL_TAC >>
  EVAL_TAC
QED

Theorem system_mstore_run[local]:
  let off = w2n (HD c.stack) in
  let sz = if op = MStore8 then 1 else 32 in
  let mx = word_size (off + sz) * 32 in
  let cost = 3 + memory_expansion_cost (buffer_length c.memory) mx in
  (op = MStore \/ op = MStore8) /\
  FLOOKUP c.msgParams.parsed c.pc = SOME op /\ c.jumpDest = NONE /\
  2 <= LENGTH c.stack /\ 
  c.gasUsed + cost <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := DROP 2 c.stack; gasUsed := c.gasUsed + cost;
      pc := c.pc + 1; memory := buffer_write off
        (if op = MStore8 then [w2w (HD (TL c.stack))]
         else REVERSE (word_to_bytes (HD (TL c.stack)) F))
        (buffer_extend (MAX (buffer_length c.memory) mx - buffer_length c.memory) c.memory)|>, rb)::cs)
Proof
  simp_tac (srw_ss()) [LET_THM] >>
  strip_tac >> Cases_on `c.stack` >> gvs[] >> Cases_on `t` >> gvs[] >>
  irule system_run_step >>
  simp[step_def, is_call_def, get_current_context_def,
    bind_def, ignore_bind_def, return_def, handle_def] >>
  simp[step_inst_def, step_mstore_def, pop_stack_def,
    memory_expansion_info_def, consume_gas_def, expand_memory_def, write_memory_def,
    inc_pc_or_jump_def, get_current_context_def, set_current_context_def,
    bind_def, ignore_bind_def, return_def, assert_def, handle_def,
    opcode_def, static_gas_def] >>
  simp[is_call_def, get_current_context_def, set_current_context_def,
    bind_def, return_def, ignore_bind_def]
QED

Theorem withdrawal_copy_address_run[local]:
  c.pc = 233 /\ c.stack = [idx; cnt; head; tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  c.gasUsed + 37 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := [4w + 3w * (idx + head); 76w * idx;
      4w + 3w * (idx + head); idx; cnt; head; tail];
      gasUsed := c.gasUsed + 37; pc := 247|>, rb)::cs)
Proof
  strip_tac >>
  `!b:byte. word_of_bytes F 0w [b] = (w2w b:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_address_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_address_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_address_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[3w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_address_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Mul`,
    `f` |-> `word_mul:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_address_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[4w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_address_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_address_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_address_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[76w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_address_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Mul`,
    `f` |-> `word_mul:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_address_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_address_parse, stack_limit_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_sender_parse[local]:
  withdrawal_instruction 248 = SOME (Push 1 [96w]) /\
  withdrawal_instruction 250 = SOME ShL /\
  withdrawal_instruction 251 = SOME (Dup 1) /\
  withdrawal_instruction 252 = SOME MStore /\
  withdrawal_instruction 253 = SOME (Push 1 [20w]) /\
  withdrawal_instruction 255 = SOME Add /\
  withdrawal_instruction 256 = SOME (Dup 1) /\
  withdrawal_instruction 257 = SOME (Push 1 [1w]) /\
  withdrawal_instruction 259 = SOME Add /\
  withdrawal_instruction 260 = SOME SLoad
Proof
  rpt conj_tac >> CONV_TAC cv_eval
QED

Theorem withdrawal_sender_run[local]:
  c.pc = 248 /\ c.stack = w0::off::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 3 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  mx = word_size (w2n off + 32) * 32 /\
  cost = memory_expansion_cost (buffer_length c.memory) mx /\
  c.gasUsed + 12 + cost <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := off::ss; pc := 253; gasUsed := c.gasUsed + 12 + cost;
      memory := buffer_write (w2n off) (REVERSE (word_to_bytes (w0 << 96) F))
        (buffer_extend (MAX (buffer_length c.memory) mx - buffer_length c.memory) c.memory)|>, rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [96w:byte] = (96w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[96w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_sender_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `ShL`,
    `f` |-> `(\n w:bytes32. w << w2n n)`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_sender_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_sender_parse, stack_limit_def] >>
  gvs[] >>
  mp_tac (Q.INST [`op` |-> `MStore`,
    `c` |-> `c with <|stack := off::(w0 << 96)::off::ss; pc := 252; gasUsed := c.gasUsed + 9|>`]
    (SRULE [LET_THM] system_mstore_run)) >>
  (impl_tac >- simp[GSYM withdrawal_instruction_def, withdrawal_sender_parse]) >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_pubkey_address_run[local]:
  c.pc = 253 /\ c.stack = off::slot::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 3 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  c.gasUsed + 15 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := (1w + slot)::(20w + off)::slot::ss;
      pc := 260; gasUsed := c.gasUsed + 15|>, rb)::cs)
Proof
  strip_tac >>
  `!b:byte. word_of_bytes F 0w [b] = (w2w b:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[20w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_sender_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_sender_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_sender_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[1w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_sender_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_sender_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_copy_first_load_run[local]:
  c.pc = 233 /\ c.stack = [idx; cnt; head; tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  s.msdomain = Collect d /\ c.gasUsed + 2137 <= c.msgParams.gasLimit ==>
  ?g keys d'. g <= c.gasUsed + 2137 /\
  run (s with contexts := (c, rb)::cs) = run (s with <|
    contexts := (c with <|pc := 248; gasUsed := g;
      stack := [lookup_storage (4w + 3w * (idx + head))
        (lookup_account c.msgParams.callee s.rollback.accounts).storage;
        76w * idx; 4w + 3w * (idx + head); idx; cnt; head; tail]|>, rb)::cs;
    rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `c.gasUsed + 37 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all withdrawal_copy_address_run >> disch_then (once_rewrite_tac o single) >>
  qabbrev_tac `slot = 4w + 3w * (idx + head)` >>
  mp_tac (Q.INST [
    `c` |-> `c with <|stack := [slot; 76w * idx; slot; idx; cnt; head; tail];
      gasUsed := c.gasUsed + 37; pc := 247|>`,
    `key` |-> `slot:bytes32`, `ss` |-> `[76w * idx; slot; idx; cnt; head; tail]`]
    system_sload_bounded_run) >>
  (impl_tac >- simp[GSYM withdrawal_instruction_def,
    withdrawal_copy_address_parse, stack_limit_def]) >>
  simp[vfmContextTheory.context_fupdcanon, Abbr `slot`] >>
  strip_tac >> qexistsl [`g`, `keys`, `d'`] >> simp[]
QED

Theorem system_swap_run[local]:
  FLOOKUP c.msgParams.parsed c.pc = SOME (Swap n) /\ n < 16 /\
  c.jumpDest = NONE /\ SUC n < LENGTH c.stack /\
  c.gasUsed + 3 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := [EL n (TL c.stack)] ++ TAKE n (TL c.stack) ++
      [HD c.stack] ++ DROP (SUC n) (TL c.stack);
      gasUsed := c.gasUsed + 3; pc := c.pc + 1|>, rb)::cs)
Proof
  strip_tac >> irule system_run_step >>
  simp[step_def, step_inst_def, step_swap_def, consume_gas_def,
    inc_pc_or_jump_def, is_call_def, opcode_def, static_gas_def,
    get_current_context_def, set_current_context_def, bind_def,
    ignore_bind_def, return_def, assert_def, handle_def]
QED

Theorem withdrawal_pubkey_parse[local]:
  withdrawal_instruction 261 = SOME (Dup 1) /\
  withdrawal_instruction 262 = SOME MStore /\
  withdrawal_instruction 263 = SOME (Push 1 [32w]) /\
  withdrawal_instruction 265 = SOME Add /\
  withdrawal_instruction 266 = SOME (Swap 0) /\
  withdrawal_instruction 267 = SOME (Push 1 [2w]) /\
  withdrawal_instruction 269 = SOME Add /\
  withdrawal_instruction 270 = SOME SLoad /\
  withdrawal_instruction 271 = SOME (Dup 0) /\
  withdrawal_instruction 272 = SOME (Push 32
    (REPLICATE 16 255w ++ REPLICATE 16 0w)) /\
  withdrawal_instruction 305 = SOME And /\
  withdrawal_instruction 306 = SOME (Dup 2) /\
  withdrawal_instruction 307 = SOME MStore /\
  withdrawal_instruction 308 = SOME (Swap 0) /\
  withdrawal_instruction 309 = SOME (Push 1 [16w]) /\
  withdrawal_instruction 311 = SOME Add /\
  withdrawal_instruction 312 = SOME (Swap 0) /\
  withdrawal_instruction 313 = SOME (Push 1 [64w]) /\
  withdrawal_instruction 315 = SOME ShR /\
  withdrawal_instruction 316 = SOME (Swap 0)
Proof
  rpt conj_tac >> CONV_TAC cv_eval
QED

Theorem withdrawal_pubkey_store_run[local]:
  c.pc = 261 /\ c.stack = w1::off::slot::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 4 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  mx = word_size (w2n off + 32) * 32 /\
  cost = memory_expansion_cost (buffer_length c.memory) mx /\
  c.gasUsed + 21 + cost <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := (2w + slot)::(32w + off)::ss; pc := 270;
      gasUsed := c.gasUsed + 21 + cost;
      memory := buffer_write (w2n off) (REVERSE (word_to_bytes w1 F))
        (buffer_extend (MAX (buffer_length c.memory) mx - buffer_length c.memory) c.memory)|>, rb)::cs)
Proof
  strip_tac >> gvs[] >>
  `!b:byte. word_of_bytes F 0w [b] = (w2w b:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `MStore`] (SRULE [LET_THM] system_mstore_run),
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[32w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_swap_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[2w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_pubkey_tail_run[local]:
  c.pc = 271 /\ c.stack = w2::off::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 4 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  mx = word_size (w2n off + 32) * 32 /\
  cost = memory_expansion_cost (buffer_length c.memory) mx /\
  c.gasUsed + 15 + cost <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := w2::off::ss; pc := 308;
      gasUsed := c.gasUsed + 15 + cost;
      memory := buffer_write (w2n off)
        (REVERSE (word_to_bytes (word_and ((-1w:bytes32) << 128) w2) F))
        (buffer_extend (MAX (buffer_length c.memory) mx - buffer_length c.memory) c.memory)|>, rb)::cs)
Proof
  strip_tac >> gvs[] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `32`,
    `ws` |-> `REPLICATE 16 (255w:byte) ++ REPLICATE 16 0w`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def,
    static_gas_def, opcode_def, withdrawal_push_mask] >>
  simp[SimpLHS, Q.INST [`op` |-> `And`,
    `f` |-> `word_and:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `MStore`] (SRULE [LET_THM] system_mstore_run),
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_amount_address_run[local]:
  c.pc = 308 /\ c.stack = w2::off::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 3 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  c.gasUsed + 21 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := (16w + off)::(w2 >>> 64)::ss; pc := 317;
      gasUsed := c.gasUsed + 21|>, rb)::cs)
Proof
  strip_tac >>
  `!b:byte. word_of_bytes F 0w [b] = (w2w b:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_swap_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[16w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_swap_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[64w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `ShR`,
    `f` |-> `\x y:bytes32. y >>> w2n x`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_swap_run,
    GSYM withdrawal_instruction_def, withdrawal_pubkey_parse] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem system_shift_byte_store_run[local]:
  c.stack = off::v::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 4 < stack_limit /\
  FLOOKUP c.msgParams.parsed c.pc = SOME (Dup 1) /\
  FLOOKUP c.msgParams.parsed (c.pc + 1) = SOME (Push 1 [sh]) /\
  FLOOKUP c.msgParams.parsed (c.pc + 3) = SOME ShR /\
  FLOOKUP c.msgParams.parsed (c.pc + 4) = SOME (Dup 1) /\
  FLOOKUP c.msgParams.parsed (c.pc + 5) = SOME (Push 1 [k]) /\
  FLOOKUP c.msgParams.parsed (c.pc + 7) = SOME Add /\
  FLOOKUP c.msgParams.parsed (c.pc + 8) = SOME MStore8 /\
  pos = w2n ((w2w k:bytes32) + off) /\
  mx = word_size (pos + 1) * 32 /\
  cost = memory_expansion_cost (buffer_length c.memory) mx /\
  c.gasUsed + 21 + cost <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := off::v::ss; pc := c.pc + 9;
      gasUsed := c.gasUsed + 21 + cost;
      memory := buffer_write pos [w2w (v >>> w2n (w2w sh:bytes32))]
        (buffer_extend (MAX (buffer_length c.memory) mx - buffer_length c.memory) c.memory)|>, rb)::cs)
Proof
  strip_tac >> gvs[] >>
  `!b:byte. word_of_bytes F 0w [b] = (w2w b:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run, stack_limit_def] >>
  simp[SimpLHS, vfmContextTheory.context_fupdcanon] >>
  Q_TAC (TRANS_TAC boolTheory.EQ_TRANS)
    `run (s with contexts := (c with <|stack := (w2w sh:bytes32)::v::off::v::ss;
      pc := c.pc + 3; gasUsed := c.gasUsed + 6|>,rb)::cs)`
  >> conj_tac
  >- (mp_tac (Q.INST [`c` |-> `c with <|stack := v::off::v::ss;
        pc := c.pc + 1; gasUsed := c.gasUsed + 3|>`,
        `n` |-> `1`, `ws` |-> `[sh:byte]`] system_push_run)
      >> simp[stack_limit_def, static_gas_def, opcode_def,
              vfmContextTheory.context_fupdcanon]) >>
  simp[SimpLHS, vfmContextTheory.context_fupdcanon] >>
  simp[SimpLHS, Q.INST [`op` |-> `ShR`,
    `f` |-> `\x y:bytes32. y >>> w2n x`] system_binop_run,
    stack_limit_def, step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, vfmContextTheory.context_fupdcanon] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run, stack_limit_def] >>
  simp[SimpLHS, vfmContextTheory.context_fupdcanon] >>
  Q_TAC (TRANS_TAC boolTheory.EQ_TRANS)
    `run (s with contexts := (c with <|stack := (w2w k:bytes32)::off::
      (v >>> w2n (w2w (sh:byte):bytes32))::off::v::ss;
      pc := c.pc + 7; gasUsed := c.gasUsed + 15|>,rb)::cs)` >> conj_tac
  >- (mp_tac (Q.INST [`c` |-> `c with <|stack := off::
        (v >>> w2n (w2w (sh:byte):bytes32))::off::v::ss;
        pc := c.pc + 5; gasUsed := c.gasUsed + 12|>`,
        `n` |-> `1`, `ws` |-> `[k:byte]`] system_push_run)
      >> simp[stack_limit_def, static_gas_def, opcode_def,
              vfmContextTheory.context_fupdcanon]) >>
  simp[SimpLHS, vfmContextTheory.context_fupdcanon] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    stack_limit_def, step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, vfmContextTheory.context_fupdcanon] >>
  simp[SimpLHS, Q.INST [`op` |-> `MStore8`] (SRULE [LET_THM] system_mstore_run)] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_request_code_correspondence:
  (lookup_account withdrawal_request_contract accounts).code = withdrawal_request_code ∧
  w2n (lookup_storage 2w (lookup_account withdrawal_request_contract accounts).storage) ≤
  w2n (lookup_storage 3w (lookup_account withdrawal_request_contract accounts).storage) ∧
  (if lookup_storage 0w (lookup_account withdrawal_request_contract accounts).storage =
        (n2w (2 ** 256 - 1) : bytes32)
   then 0 else w2n (lookup_storage 0w
                       (lookup_account withdrawal_request_contract accounts).storage)) +
  w2n (lookup_storage 1w (lookup_account withdrawal_request_contract accounts).storage) <
    2 ** 256 ⇒
  ∃d'. run_system_transaction T (Collect d) chainId prevHashes blk accounts
         withdrawal_request_contract [] =
       SOME (FLAT (FST (dequeue_withdrawal_requests accounts)),
             SND (dequeue_withdrawal_requests accounts), Collect d')
Proof
  cheat
QED

Theorem consolidation_request_code_correspondence:
  (lookup_account consolidation_request_contract accounts).code = consolidation_request_code ∧
  w2n (lookup_storage 2w (lookup_account consolidation_request_contract accounts).storage) ≤
  w2n (lookup_storage 3w (lookup_account consolidation_request_contract accounts).storage) ∧
  (if lookup_storage 0w (lookup_account consolidation_request_contract accounts).storage =
        (n2w (2 ** 256 - 1) : bytes32)
   then 0 else w2n (lookup_storage 0w
                       (lookup_account consolidation_request_contract accounts).storage)) +
  w2n (lookup_storage 1w (lookup_account consolidation_request_contract accounts).storage) <
    2 ** 256 ⇒
  ∃d'. run_system_transaction T (Collect d) chainId prevHashes blk accounts
         consolidation_request_contract [] =
       SOME (FLAT (FST (dequeue_consolidation_requests accounts)),
             SND (dequeue_consolidation_requests accounts), Collect d')
Proof
  cheat
QED
