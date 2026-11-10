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
  cheat
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

Theorem history_storage_code_correspondence:
  (lookup_account history_storage_address accounts).code = history_storage_code ∧
  0 < blk.number ∧ blk.number < 2 ** 256 ⇒
  ∃d'. run_system_transaction F (Collect d) chainId prevHashes blk accounts
         history_storage_address (word_to_bytes parent_hash T) =
       SOME ([], update_history_block [parent_hash] blk accounts, Collect d')
Proof
  cheat
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
