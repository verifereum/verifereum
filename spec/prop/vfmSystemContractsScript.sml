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

Theorem system_return_inst[local]:
  c.stack = [offset;sz] /\
  mx = (if 0 < w2n sz then word_size (w2n offset+w2n sz)*32 else 0) /\
  cost = memory_expansion_cost (buffer_length c.memory) mx /\
  mem = buffer_extend (MAX (buffer_length c.memory) mx-buffer_length c.memory) c.memory /\
  c.gasUsed+cost <= c.msgParams.gasLimit ==>
  step_return T (s with contexts := (c,rb)::cs) =
    ((INR NONE : unit + exception option), s with contexts := (c with <|stack := []; gasUsed := c.gasUsed+cost;
      memory := mem; returnData := buffer_take (w2n offset) (w2n sz) mem|>,rb)::cs)
Proof
  strip_tac >>
  simp[step_return_def, pop_stack_def, assert_def,
    get_current_context_def, set_current_context_def,
    bind_def, ignore_bind_def, return_def] >>
  simp[memory_expansion_info_def, get_current_context_def, return_def, bind_def,
    GSYM arithmeticTheory.MULT_ASSOC] >>
  qpat_assum `mx = _` (fn th => pure_rewrite_tac [GSYM (SRULE [] th)]) >>
  qpat_assum `cost = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  simp[consume_gas_def, get_current_context_def, set_current_context_def,
    bind_def, ignore_bind_def, return_def, assert_def] >>
  simp[expand_memory_def, get_current_context_def, set_current_context_def,
    bind_def, return_def] >>
  simp[read_memory_def, set_return_data_def, finish_def,
    get_current_context_def, set_current_context_def, bind_def, return_def,
    ignore_bind_def, vfmContextTheory.context_fupdcanon] >> gvs[]
QED

Theorem system_return_run:
  c.stack = [offset;sz] /\ c.msgParams.outputTo = empty_return_destination /\
  FLOOKUP c.msgParams.parsed c.pc = SOME Return /\
  mx = (if 0 < w2n sz then word_size (w2n offset+w2n sz)*32 else 0) /\
  cost = memory_expansion_cost (buffer_length c.memory) mx /\
  mem = buffer_extend (MAX (buffer_length c.memory) mx-buffer_length c.memory) c.memory /\
  c.gasUsed+cost <= c.msgParams.gasLimit ==>
  run (s with contexts := [(c,rb)]) =
    SOME (INR NONE, s with contexts := [(c with <|stack := []; gasUsed := c.gasUsed+cost;
      memory := mem; returnData := buffer_take (w2n offset) (w2n sz) mem|>,rb)])
Proof
  strip_tac >>
  drule_all system_return_inst >>
  disch_then (qspecl_then [`s`, `rb`, `[]`] assume_tac) >>
  simp[vfmDecreasesGasTheory.run_eq_tr] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def, step_def, step_inst_def] >>
  simp[handle_def, get_current_context_def, bind_def, ignore_bind_def,
    return_def, step_inst_def] >>
  simp[handle_step_def, vfm_abort_def, handle_create_def, handle_exception_def,
    get_return_data_def, get_output_to_def, get_num_contexts_def,
    get_current_context_def, set_current_context_def, bind_def, ignore_bind_def,
    return_def, reraise_def, handle_def, vfmContextTheory.empty_return_destination_def] >>
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

Theorem system_sstore_bounded_run:
  c.stack = key::value::ss /\ c.jumpDest = NONE /\ ~c.msgParams.static /\
  FLOOKUP c.msgParams.parsed c.pc = SOME SStore /\ s.msdomain = Collect d /\
  c.gasUsed + 22100 <= c.msgParams.gasLimit ==>
  ?g ad su keys d'. g <= c.gasUsed + 22100 /\
  run (s with contexts := (c, rb)::cs) =
  run (s with <|
    contexts := (c with <|pc := c.pc + 1; stack := ss; gasUsed := g;
      addRefund := ad + c.addRefund; subRefund := su + c.subRefund|>, rb)::cs;
    rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          update_storage key value) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  qabbrev_tac `current = lookup_storage key
    (lookup_account c.msgParams.callee s.rollback.accounts).storage` >>
  qabbrev_tac `original = lookup_storage key
    (lookup_account c.msgParams.callee s.originalAccounts).storage` >>
  qabbrev_tac `cost = sstore_base_gas original current value +
    zero_warm (if fIN (SK c.msgParams.callee key) s.rollback.accesses.storageKeys
      then warm_access_cost else cold_sload_cost)` >>
  `cost <= 22100` by
    (simp[Abbr `cost`, sstore_base_gas_def, zero_warm_def,
      storage_set_cost_def, storage_update_cost_def,
      cold_sload_cost_def, warm_access_cost_def] >>
     rpt IF_CASES_TAC >> simp[]) >>
  Cases_on `sstore_refund_updates original current value` >>
  rename1 `sstore_refund_updates original current value = (ad,su)` >>
  qexistsl [`c.gasUsed + cost`, `ad`, `su`,
    `fINSERT (SK c.msgParams.callee key) s.rollback.accesses.storageKeys`,
    `d with storageKeys updated_by fINSERT (SK c.msgParams.callee key)`] >>
  conj_tac >- decide_tac >>
  mp_tac (Q.INST [`address` |-> `c.msgParams.callee`,
    `current` |-> `current`, `original` |-> `original`, `cost` |-> `cost`,
    `ad` |-> `ad`, `su` |-> `su`] system_sstore_run) >>
  (impl_tac >- (simp[Abbr `current`, Abbr `original`, Abbr `cost`,
    call_stipend_def] >> decide_tac)) >>
  Cases_on `s.rollback.accesses` >>
  simp[vfmContextTheory.access_sets_fn_updates]
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
  simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_txParams_def,
    step_binop_def, step_dup_def, get_tx_params_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_txParams_def,
    step_binop_def, step_dup_def, get_tx_params_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_txParams_def,
    step_binop_def, step_dup_def, get_tx_params_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_txParams_def,
    step_binop_def, step_dup_def, get_tx_params_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_txParams_def,
    step_binop_def, step_dup_def, get_tx_params_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse]
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
  simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_call_data_load_def,
    step_swap_def, step_binop_def, get_call_data_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def, CONJUNCT1 byteTheory.word_of_bytes_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_call_data_load_def,
    step_swap_def, step_binop_def, get_call_data_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def, CONJUNCT1 byteTheory.word_of_bytes_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_call_data_load_def,
    step_swap_def, step_binop_def, get_call_data_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def, CONJUNCT1 byteTheory.word_of_bytes_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_call_data_load_def,
    step_swap_def, step_binop_def, get_call_data_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def, CONJUNCT1 byteTheory.word_of_bytes_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse] >>
  simp[Once vfmDecreasesGasTheory.run_tr_def,
    step_def, step_inst_def, step_push_def, step_call_data_load_def,
    step_swap_def, step_binop_def, get_call_data_def,
    consume_gas_def, push_stack_def, pop_stack_def, inc_pc_or_jump_def,
    is_call_def, static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def, stack_limit_def, CONJUNCT1 byteTheory.word_of_bytes_def,
    GSYM beacon_roots_instruction_def, beacon_roots_parse]
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

Theorem queue_sender_bytes:
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

Theorem queue_read_el:
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

Theorem queue_read_extend:
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

Theorem queue_read_write_el:
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

Theorem queue_read_write_cong:
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

Theorem queue_read_write_extend:
  buffer_read off sz (buffer_write p bs (buffer_extend n b)) =
  buffer_read off sz (buffer_write p bs b)
Proof
  irule queue_read_write_cong >> simp[queue_read_extend]
QED

Theorem queue_take_read:
  off + sz <= buffer_length b ==>
  buffer_take off sz b = buffer_read off sz b
Proof
  strip_tac
  >> simp[vfmBufferTheory.buffer_take_to_list,
          vfmBufferTheory.buffer_read_to_list, take_pad_0_def,
          listTheory.PAD_RIGHT, listTheory.LENGTH_TAKE_EQ,
          vfmBufferTheory.LENGTH_buffer_to_list]
QED

Theorem queue_take_read_cong:
  (!off sz. buffer_read off sz b = buffer_read off sz b') /\
  off + sz <= buffer_length b /\ off + sz <= buffer_length b' ==>
  buffer_take off sz b = buffer_take off sz b'
Proof
  simp[queue_take_read]
QED

Theorem queue_write_prefix:
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

Theorem queue_write_byte_tail:
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

Theorem queue_pubkey_bytes:
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

Theorem queue_amount_bytes:
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

Theorem system_sload_step:
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

Theorem system_push_run:
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

Theorem system_push1_sstore_run:
  FLOOKUP c.msgParams.parsed c.pc = SOME (Push 1 [slot]) /\
  FLOOKUP c.msgParams.parsed (c.pc+2) = SOME SStore /\
  c.stack = value::ss /\ c.jumpDest = NONE /\ ~c.msgParams.static /\
  LENGTH c.stack < stack_limit /\ s.msdomain = Collect d /\
  c.gasUsed+22103 <= c.msgParams.gasLimit ==>
  ?g ad su keys d'. g <= c.gasUsed+22103 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := c.pc+3; stack := ss; gasUsed := g;
      addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>,rb)::cs;
    rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          update_storage (w2w slot) value) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `word_of_bytes F 0w [slot] = (w2w slot:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  qabbrev_tac `c1 = c with <|stack := word_of_bytes F 0w (REVERSE [slot])::c.stack;
    gasUsed := c.gasUsed+static_gas (Push 1 [slot]);
    pc := c.pc+LENGTH (opcode (Push 1 [slot]))|>` >>
  `run (s with contexts := (c,rb)::cs) = run (s with contexts := (c1,rb)::cs)` by
    (simp_tac pure_ss [Abbr `c1`] >> irule system_push_run >>
     simp[static_gas_def]) >>
  mp_tac (Q.INST [`c` |-> `c1`, `key` |-> `w2w (slot:byte):bytes32`]
    system_sstore_bounded_run) >>
  (impl_tac >- simp[Abbr `c1`, static_gas_def, opcode_def]) >>
  simp[Abbr `c1`, static_gas_def, opcode_def, vfmContextTheory.context_fupdcanon] >>
  strip_tac >> qexistsl [`g`, `ad`, `su`, `keys`, `d'`] >> simp[]
QED

Theorem system_clear_slot_run:
  FLOOKUP c.msgParams.parsed c.pc = SOME (Push 0 []) /\
  FLOOKUP c.msgParams.parsed (c.pc+1) = SOME (Push 1 [slot]) /\
  FLOOKUP c.msgParams.parsed (c.pc+3) = SOME SStore /\
  c.jumpDest = NONE /\ ~c.msgParams.static /\
  LENGTH c.stack+1 < stack_limit /\ s.msdomain = Collect d /\
  c.gasUsed+22105 <= c.msgParams.gasLimit ==>
  ?g ad su keys d'. g <= c.gasUsed+22105 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := c.pc+4; gasUsed := g;
      addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>,rb)::cs;
    rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          update_storage (w2w slot) 0w) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  qabbrev_tac `c1 = c with <|stack := word_of_bytes F 0w (REVERSE [])::c.stack;
    gasUsed := c.gasUsed+static_gas (Push 0 []);
    pc := c.pc+LENGTH (opcode (Push 0 []))|>` >>
  `run (s with contexts := (c,rb)::cs) = run (s with contexts := (c1,rb)::cs)` by
    (simp_tac pure_ss [Abbr `c1`] >> irule system_push_run >>
     gvs[static_gas_def, stack_limit_def]) >>
  mp_tac (Q.INST [`c` |-> `c1`, `slot` |-> `slot:byte`,
    `value` |-> `0w:bytes32`, `ss` |-> `c.stack`] system_push1_sstore_run) >>
  (impl_tac >- gvs[Abbr `c1`, static_gas_def, opcode_def,
    byteTheory.word_of_bytes_def, stack_limit_def]) >>
  simp[Abbr `c1`, static_gas_def, opcode_def, byteTheory.word_of_bytes_def,
    vfmContextTheory.context_fupdcanon] >>
  strip_tac >> qexistsl [`g`, `ad`, `su`, `keys`, `d'`] >> simp[] >>
  Cases_on `c` >> gvs[vfmContextTheory.context_fn_updates]
QED

Theorem system_sload_bounded_run:
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

Theorem system_push1_sload_run:
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

Theorem system_dup_run:
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

Theorem system_binop_run:
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

Theorem system_monop_run:
  c.stack <> [] /\ c.jumpDest = NONE /\ LENGTH c.stack <= stack_limit /\
  FLOOKUP c.msgParams.parsed c.pc = SOME op /\
  step_inst op = step_monop op f /\ ~is_call op /\ LENGTH (opcode op) = 1 /\
  c.gasUsed+static_gas op <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|stack := f (HD c.stack)::TL c.stack;
      gasUsed := c.gasUsed+static_gas op; pc := c.pc+1|>,rb)::cs)
Proof
  strip_tac >> Cases_on `c.stack` >> gvs[] >>
  irule system_run_step >>
  simp[step_def, step_monop_def, consume_gas_def, push_stack_def, pop_stack_def,
    inc_pc_or_jump_def, get_current_context_def, set_current_context_def, bind_def,
    ignore_bind_def, return_def, assert_def, handle_def, stack_limit_def]
QED

Theorem system_jumpi_run:
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

Theorem system_pop_run:
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

Theorem system_mstore_run:
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

Theorem system_swap_run:
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

Theorem system_shift_byte_store_run:
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

Theorem withdrawal_amount_parse[local]:
  j < 7 ==>
  withdrawal_instruction (317 + 9*j) = SOME (Dup 1) /\
  withdrawal_instruction (318 + 9*j) = SOME (Push 1 [n2w (56 - 8*j)]) /\
  withdrawal_instruction (320 + 9*j) = SOME ShR /\
  withdrawal_instruction (321 + 9*j) = SOME (Dup 1) /\
  withdrawal_instruction (322 + 9*j) = SOME (Push 1 [n2w (7-j)]) /\
  withdrawal_instruction (324 + 9*j) = SOME Add /\
  withdrawal_instruction (325 + 9*j) = SOME MStore8
Proof
  strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6` by decide_tac >>
  gvs[] >> rpt conj_tac >> CONV_TAC cv_eval
QED

Theorem withdrawal_amount_byte_run[local]:
  j < 7 /\ c.pc = 317 + 9*j /\
  c.stack = off::v::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 4 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  pos = w2n ((n2w (7-j):bytes32) + off) /\
  mx = word_size (pos + 1) * 32 /\
  cost = memory_expansion_cost (buffer_length c.memory) mx /\
  c.gasUsed + 21 + cost <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := off::v::ss; pc := 326 + 9*j;
      gasUsed := c.gasUsed + 21 + cost;
      memory := buffer_write pos [w2w (v >>> (56 - 8*j))]
        (buffer_extend (MAX (buffer_length c.memory) mx - buffer_length c.memory) c.memory)|>, rb)::cs)
Proof
  strip_tac >>
  drule withdrawal_amount_parse >> strip_tac >>
  mp_tac (Q.INST [`sh` |-> `n2w (56 - 8*j):byte`,
    `k` |-> `n2w (7-j):byte`] system_shift_byte_store_run) >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6` by decide_tac >>
  gvs[GSYM withdrawal_instruction_def, wordsTheory.w2w_n2w,
    wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem system_jump_run:
  c.stack <> [] /\ c.jumpDest = NONE /\
  FLOOKUP c.msgParams.parsed c.pc = SOME Jump /\
  FLOOKUP c.msgParams.parsed (w2n (HD c.stack)) = SOME JumpDest /\
  w2n (HD c.stack) < LENGTH c.msgParams.code /\
  c.gasUsed + 8 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := TL c.stack; pc := w2n (HD c.stack);
      gasUsed := c.gasUsed + 8|>, rb)::cs)
Proof
  strip_tac >> Cases_on `c.stack` >> gvs[] >>
  irule system_run_step >>
  simp[step_def, step_inst_def, step_jump_def, pop_stack_def,
    consume_gas_def, set_jump_dest_def, inc_pc_or_jump_def, is_call_def,
    static_gas_def, opcode_def, get_current_context_def,
    set_current_context_def, bind_def, ignore_bind_def, return_def,
    assert_def, handle_def] >>
  Cases_on `c` >> gvs[vfmContextTheory.context_fn_updates]
QED

Theorem withdrawal_copy_backedge_parse[local]:
  withdrawal_instruction 380 = SOME MStore8 /\
  withdrawal_instruction 381 = SOME (Push 1 [1w]) /\
  withdrawal_instruction 383 = SOME Add /\
  withdrawal_instruction 384 = SOME (Push 1 [225w]) /\
  withdrawal_instruction 386 = SOME Jump
Proof
  rpt conj_tac >> CONV_TAC cv_eval
QED

Theorem withdrawal_amount_final_run[local]:
  c.pc = 380 /\ c.stack = off::v::i::ss /\ c.jumpDest = NONE /\
  225 < LENGTH c.msgParams.code /\
  LENGTH ss + 3 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  mx = word_size (w2n off + 1) * 32 /\
  cost = memory_expansion_cost (buffer_length c.memory) mx /\
  c.gasUsed + 20 + cost <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := (1w+i)::ss; pc := 225;
      gasUsed := c.gasUsed + 20 + cost;
      memory := buffer_write (w2n off) [w2w v]
        (buffer_extend (MAX (buffer_length c.memory) mx - buffer_length c.memory) c.memory)|>, rb)::cs)
Proof
  strip_tac >> gvs[] >>
  `!b:byte. word_of_bytes F 0w [b] = (w2w b:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`op` |-> `MStore8`] (SRULE [LET_THM] system_mstore_run),
    GSYM withdrawal_instruction_def, withdrawal_copy_backedge_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[1w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_backedge_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_backedge_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[225w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_copy_backedge_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, system_jump_run, GSYM withdrawal_instruction_def,
    withdrawal_copy_backedge_parse, withdrawal_entry_parse] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem queue_aligned_allocation:
  L MOD 32 = 0 /\ x <= L ==> word_size x * 32 <= L
Proof
  simp[word_size_def] >> intLib.COOPER_TAC
QED

Theorem queue_allocated_expansion:
  buffer_length b MOD 32 = 0 /\ x <= buffer_length b ==>
  memory_expansion_cost (buffer_length b) (word_size x * 32) = 0 /\
  buffer_extend (MAX (buffer_length b) (word_size x * 32) - buffer_length b) b = b
Proof
  strip_tac >> drule_all queue_aligned_allocation >>
  simp[memory_expansion_cost_def, arithmeticTheory.MAX_DEF]
QED

Theorem withdrawal_amount_byte_allocated_run[local]:
  j < 7 /\ c.pc = 317 + 9*j /\ 2 <= LENGTH c.stack /\
  c.jumpDest = NONE /\ LENGTH c.stack + 2 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  w2n (HD c.stack) + 8 < 2 ** 256 /\
  w2n (HD c.stack) + 8 <= buffer_length c.memory /\
  buffer_length c.memory MOD 32 = 0 /\
  c.gasUsed + 21 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|pc := 326 + 9*j; gasUsed := c.gasUsed + 21;
      memory := buffer_write (w2n (HD c.stack) + (7-j))
        [w2w (HD (TL c.stack) >>> (56-8*j))] c.memory|>, rb)::cs)
Proof
  strip_tac >> Cases_on `c.stack` >> gvs[] >> Cases_on `t` >> gvs[] >>
  `w2n ((n2w (7-j):bytes32) + h) = w2n h + (7-j)` by
    (simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, wordsTheory.dimword_def]) >>
  `w2n h + (7-j) + 1 <= buffer_length c.memory` by decide_tac >>
  drule_all queue_allocated_expansion >> strip_tac >>
  drule_at (Pat `c.stack = off::v::ss`)
    (Q.INST [`pos` |-> `w2n (HD c.stack) + (7-j)`,
      `mx` |-> `word_size (w2n (HD c.stack) + (7-j) + 1) * 32`, `cost` |-> `0`]
      withdrawal_amount_byte_run) >>
  `c with stack := h::h'::t' = c` by metis_tac[vfmContextTheory.context_fupdselfid] >>
  simp[wordsTheory.WORD_ADD_COMM] >>
  disch_then (qspecl_then [`s`, `rb`, `cs`] mp_tac) >>
  gs[wordsTheory.WORD_ADD_COMM] >>
  Cases_on `c` >> gvs[vfmContextTheory.context_fn_updates]
QED

Theorem withdrawal_amount_final_allocated_run[local]:
  c.pc = 380 /\ 3 <= LENGTH c.stack /\ c.jumpDest = NONE /\
  LENGTH c.stack + 2 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  225 < LENGTH c.msgParams.code /\
  w2n (HD c.stack) + 1 <= buffer_length c.memory /\
  buffer_length c.memory MOD 32 = 0 /\
  c.gasUsed + 20 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := (1w + HD (DROP 2 c.stack))::DROP 3 c.stack;
      pc := 225; gasUsed := c.gasUsed + 20;
      memory := buffer_write (w2n (HD c.stack)) [w2w (HD (TL c.stack))] c.memory|>, rb)::cs)
Proof
  strip_tac >> Cases_on `c.stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  drule_all queue_allocated_expansion >> strip_tac >>
  drule_at (Pat `c.stack = off::v::i::ss`)
    (Q.INST [`mx` |-> `word_size (w2n (HD c.stack) + 1) * 32`, `cost` |-> `0`]
      withdrawal_amount_final_run) >>
  gvs[]
QED

Theorem withdrawal_amount_allocated_run[local]:
  c.pc = 317 /\ c.stack = n2w p::v::idx::ss /\ c.jumpDest = NONE /\
  p + 8 < 2 ** 256 /\ p + 8 <= buffer_length c.memory /\
  buffer_length c.memory MOD 32 = 0 /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  225 < LENGTH c.msgParams.code /\ LENGTH ss + 5 < stack_limit /\
  c.gasUsed + 167 <= c.msgParams.gasLimit ==>
  let b1 = buffer_write (p+7) [w2w (v >>> 56)] c.memory in
  let b2 = buffer_write (p+6) [w2w (v >>> 48)] b1 in
  let b3 = buffer_write (p+5) [w2w (v >>> 40)] b2 in
  let b4 = buffer_write (p+4) [w2w (v >>> 32)] b3 in
  let b5 = buffer_write (p+3) [w2w (v >>> 24)] b4 in
  let b6 = buffer_write (p+2) [w2w (v >>> 16)] b5 in
  let b7 = buffer_write (p+1) [w2w (v >>> 8)] b6 in
  let m = buffer_write p [w2w v] b7 in
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := (1w+idx)::ss; pc := 225;
      gasUsed := c.gasUsed + 167; memory := m|>, rb)::cs) /\
  buffer_length m = buffer_length c.memory
Proof
  strip_tac >> simp_tac pure_ss [LET_THM] >>
  `w2n (n2w p:bytes32) = p` by gvs[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  gs[stack_limit_def, wordsTheory.dimword_def] >>
  qmatch_goalsub_abbrev_tac `buffer_write (p+6) _ b1` >>
  qmatch_goalsub_abbrev_tac `buffer_write (p+5) _ b2` >>
  qmatch_goalsub_abbrev_tac `buffer_write (p+4) _ b3` >>
  qmatch_goalsub_abbrev_tac `buffer_write (p+3) _ b4` >>
  qmatch_goalsub_abbrev_tac `buffer_write (p+2) _ b5` >>
  qmatch_goalsub_abbrev_tac `buffer_write (p+1) _ b6` >>
  qmatch_goalsub_abbrev_tac `buffer_write p _ b7` >>
  `buffer_length b1 = buffer_length c.memory` by simp[Abbr `b1`, arithmeticTheory.MAX_DEF] >>
  `buffer_length b2 = buffer_length c.memory` by simp[Abbr `b2`, arithmeticTheory.MAX_DEF] >>
  `buffer_length b3 = buffer_length c.memory` by simp[Abbr `b3`, arithmeticTheory.MAX_DEF] >>
  `buffer_length b4 = buffer_length c.memory` by simp[Abbr `b4`, arithmeticTheory.MAX_DEF] >>
  `buffer_length b5 = buffer_length c.memory` by simp[Abbr `b5`, arithmeticTheory.MAX_DEF] >>
  `buffer_length b6 = buffer_length c.memory` by simp[Abbr `b6`, arithmeticTheory.MAX_DEF] >>
  `buffer_length b7 = buffer_length c.memory` by simp[Abbr `b7`, arithmeticTheory.MAX_DEF] >>
  reverse conj_tac >- simp[arithmeticTheory.MAX_DEF] >>
  simp[SimpLHS, Q.INST [`j` |-> `0`] withdrawal_amount_byte_allocated_run,
    Excl "buffer_length_write"] >>
  simp[SimpLHS, Q.INST [`j` |-> `1`] withdrawal_amount_byte_allocated_run,
    Excl "buffer_length_write"] >>
  simp[SimpLHS, Q.INST [`j` |-> `2`] withdrawal_amount_byte_allocated_run,
    Excl "buffer_length_write"] >>
  simp[SimpLHS, Q.INST [`j` |-> `3`] withdrawal_amount_byte_allocated_run,
    Excl "buffer_length_write"] >>
  simp[SimpLHS, Q.INST [`j` |-> `4`] withdrawal_amount_byte_allocated_run,
    Excl "buffer_length_write"] >>
  simp[SimpLHS, Q.INST [`j` |-> `5`] withdrawal_amount_byte_allocated_run,
    Excl "buffer_length_write"] >>
  simp[SimpLHS, Q.INST [`j` |-> `6`] withdrawal_amount_byte_allocated_run,
    Excl "buffer_length_write"] >>
  simp[SimpLHS, withdrawal_amount_final_allocated_run, Excl "buffer_length_write"] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem queue_memory_cost_bound:
  n <= 1280 ==> memory_cost n <= 123
Proof
  strip_tac >>
  `word_size n <= 40` by (simp[word_size_def] >> intLib.COOPER_TAC) >>
  `word_size n * word_size n <= 1600` by
    (mp_tac (Q.SPECL [`word_size n`, `word_size n`, `40`, `40`]
      arithmeticTheory.LESS_MONO_MULT2) >> simp[]) >>
  simp[memory_cost_def, memory_cost_per_word_def] >>
  `word_size n * word_size n DIV 512 <= 3` by
    (simp[arithmeticTheory.DIV_LE_X] >> gvs[]) >>
  gvs[]
QED

Theorem queue_expanded_word_length:
  p + 32 <= 1280 /\ buffer_length b <= 1280 /\
  buffer_length b MOD 32 = 0 ==>
  let mx = word_size (p + 32) * 32 in
  let m = buffer_write p (word_to_bytes (w:bytes32) T)
    (buffer_extend (MAX (buffer_length b) mx - buffer_length b) b) in
  buffer_length m = MAX (buffer_length b) mx /\
  p + 32 <= buffer_length m /\ buffer_length m <= 1280 /\
  buffer_length m MOD 32 = 0 /\
  memory_expansion_cost (buffer_length b) mx <= 123
Proof
  strip_tac >> simp_tac (srw_ss()) [LET_THM] >>
  `p + 32 <= word_size (p + 32) * 32 /\
   word_size (p + 32) * 32 <= 1280 /\
   (word_size (p + 32) * 32) MOD 32 = 0` by
    (simp[word_size_def] >> intLib.COOPER_TAC) >>
  `memory_cost (MAX (buffer_length b) (word_size (p + 32) * 32)) <= 123` by
    (irule queue_memory_cost_bound >> simp[arithmeticTheory.MAX_DEF]) >>
  simp[byteTheory.LENGTH_word_to_bytes, arithmeticTheory.MAX_DEF,
    memory_expansion_cost_def] >>
  rpt IF_CASES_TAC >> gvs[arithmeticTheory.MAX_DEF] >> intLib.COOPER_TAC
QED

Theorem withdrawal_expanded_record_memory[local]:
  i < 16 /\ 76*i <= buffer_length b /\ buffer_length b <= 1280 /\
  buffer_length b MOD 32 = 0 ==>
  let off = 76*i in
  let base = 4 + (h+i)*3 in
  let w0 = lookup_storage (n2w base) storage in
  let w1 = lookup_storage (n2w (base+1)) storage in
  let w2 = lookup_storage (n2w (base+2)) storage in
  let a = w2 >>> 64 in
  let mx1 = word_size (off+32)*32 in
  let m1 = buffer_write off (word_to_bytes (w0 << 96) T)
    (buffer_extend (MAX (buffer_length b) mx1 - buffer_length b) b) in
  let mx2 = word_size (off+52)*32 in
  let m2 = buffer_write (off+20) (word_to_bytes w1 T)
    (buffer_extend (MAX (buffer_length m1) mx2 - buffer_length m1) m1) in
  let mx3 = word_size (off+84)*32 in
  let m3 = buffer_write (off+52) (word_to_bytes (w2 && (-1w << 128)) T)
    (buffer_extend (MAX (buffer_length m2) mx3 - buffer_length m2) m2) in
  let m4 = buffer_write (off+75) [w2w (a >>> 56)] m3 in
  let m5 = buffer_write (off+74) [w2w (a >>> 48)] m4 in
  let m6 = buffer_write (off+73) [w2w (a >>> 40)] m5 in
  let m7 = buffer_write (off+72) [w2w (a >>> 32)] m6 in
  let m8 = buffer_write (off+71) [w2w (a >>> 24)] m7 in
  let m9 = buffer_write (off+70) [w2w (a >>> 16)] m8 in
  let m10 = buffer_write (off+69) [w2w (a >>> 8)] m9 in
  let m11 = buffer_write (off+68) [w2w a] m10 in
  memory_expansion_cost (buffer_length b) mx1 <= 123 /\
  memory_expansion_cost (buffer_length m1) mx2 <= 123 /\
  memory_expansion_cost (buffer_length m2) mx3 <= 123 /\
  off+84 <= buffer_length m3 /\
  buffer_length m11 = buffer_length m3 /\
  off+76 <= buffer_length m11 /\ buffer_length m11 <= 1280 /\
  buffer_length m11 MOD 32 = 0 /\
  buffer_take 0 (off+76) m11 =
    buffer_take 0 off b ++ read_withdrawal_request storage (h+i)
Proof
  strip_tac >> rpt BasicProvers.LET_ELIM_TAC >>
  `off + 84 <= 1280` by (simp[Abbr `off`] >> decide_tac) >>
  `buffer_length m1 <= 1280 /\ buffer_length m1 MOD 32 = 0 /\
   memory_expansion_cost (buffer_length b) mx1 <= 123` by
    (mp_tac (Q.INST [`p` |-> `off`, `w` |-> `w0 << 96`]
      queue_expanded_word_length) >>
     simp[Abbr `m1`, Abbr `mx1`, LET_THM,
       Excl "buffer_length_write", Excl "buffer_length_extend"] >> strip_tac >> gvs[]) >>
  `buffer_length m2 <= 1280 /\ buffer_length m2 MOD 32 = 0 /\
   memory_expansion_cost (buffer_length m1) mx2 <= 123` by
    (mp_tac (Q.INST [`p` |-> `off+20`, `w` |-> `w1`, `b` |-> `m1`]
      queue_expanded_word_length) >>
     simp[Abbr `m2`, Abbr `mx2`, LET_THM,
       Excl "buffer_length_write", Excl "buffer_length_extend"] >> strip_tac >> gvs[]) >>
  `off+84 <= buffer_length m3 /\ buffer_length m3 <= 1280 /\
   buffer_length m3 MOD 32 = 0 /\
   memory_expansion_cost (buffer_length m2) mx3 <= 123` by
    (mp_tac (Q.INST [`p` |-> `off+52`, `w` |-> `w2 && (-1w << 128)`,
      `b` |-> `m2`] queue_expanded_word_length) >>
     simp[Abbr `m3`, Abbr `mx3`, LET_THM,
       Excl "buffer_length_write", Excl "buffer_length_extend"] >> strip_tac >> gvs[]) >>
  `buffer_length m4 = buffer_length m3` by simp[Abbr `m4`, arithmeticTheory.MAX_DEF] >>
  `buffer_length m5 = buffer_length m3` by simp[Abbr `m5`, arithmeticTheory.MAX_DEF] >>
  `buffer_length m6 = buffer_length m3` by simp[Abbr `m6`, arithmeticTheory.MAX_DEF] >>
  `buffer_length m7 = buffer_length m3` by simp[Abbr `m7`, arithmeticTheory.MAX_DEF] >>
  `buffer_length m8 = buffer_length m3` by simp[Abbr `m8`, arithmeticTheory.MAX_DEF] >>
  `buffer_length m9 = buffer_length m3` by simp[Abbr `m9`, arithmeticTheory.MAX_DEF] >>
  `buffer_length m10 = buffer_length m3` by simp[Abbr `m10`, arithmeticTheory.MAX_DEF] >>
  `buffer_length m11 = buffer_length m3` by simp[Abbr `m11`, arithmeticTheory.MAX_DEF] >>
  simp[Excl "buffer_length_write"] >>
  mp_tac (Q.INST [`idx` |-> `h+i`] withdrawal_record_memory) >>
  (impl_tac >- simp[]) >> simp_tac pure_ss [LET_THM] >>
  disch_then (fn th => once_rewrite_tac[GSYM th]) >>
  irule queue_take_read_cong >> conj_tac
  >- (rpt gen_tac >>
      simp_tac (srw_ss()) [Abbr `m11`, Abbr `m10`, Abbr `m9`, Abbr `m8`,
        Abbr `m7`, Abbr `m6`, Abbr `m5`, Abbr `m4`, Abbr `m3`, Abbr `m2`,
        Abbr `m1`, Abbr `a`, Abbr `w0`, Abbr `w1`, Abbr `w2`, Abbr `base'`,
        queue_read_write_extend] >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      rpt (irule queue_read_write_cong >> rpt gen_tac >>
        simp_tac pure_ss [queue_read_write_extend]) >> simp[]) >>
  conj_tac >- simp[Excl "buffer_length_write"] >>
  ntac 8 (irule vfmBufferTheory.buffer_write_preserves_coverage) >>
  irule vfmBufferTheory.buffer_write_covers_endpoint >>
  simp[byteTheory.LENGTH_word_to_bytes, Excl "buffer_length_write"] >>
  pure_once_rewrite_tac[GSYM listTheory.LENGTH_NIL] >>
  pure_rewrite_tac[byteTheory.LENGTH_word_to_bytes] >> simp[]
QED

Theorem withdrawal_record_run[local]:
  c.pc = 233 /\ c.stack = [n2w i; cnt; head; tail] /\
  c.jumpDest = NONE /\ i < 16 /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  225 < LENGTH c.msgParams.code /\ s.msdomain = Collect d /\
  76*i <= buffer_length c.memory /\ buffer_length c.memory <= 1280 /\
  buffer_length c.memory MOD 32 = 0 /\
  c.gasUsed + 7100 <= c.msgParams.gasLimit ==>
  ?g keys d' m. g <= c.gasUsed + 7100 /\
    run (s with contexts := (c, rb)::cs) = run (s with <|
      contexts := (c with <|pc := 225; stack := [n2w (i+1); cnt; head; tail];
        gasUsed := g; memory := m|>, rb)::cs;
      rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
      msdomain := Collect d'|>) /\
    buffer_take 0 (76*(i+1)) m = buffer_take 0 (76*i) c.memory ++
      read_withdrawal_request
        (lookup_account c.msgParams.callee s.rollback.accounts).storage (w2n head+i) /\
    76*(i+1) <= buffer_length m /\ buffer_length m <= 1280 /\
    buffer_length m MOD 32 = 0
Proof
  strip_tac >>
  `c.gasUsed + 2137 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all withdrawal_copy_first_load_run >>
  disch_then (qspecl_then [`rb`, `cs`]
    (qx_choosel_then [`g1`, `keys1`, `d1`] strip_assume_tac)) >>
  qabbrev_tac `slot = 4w + 3w * (n2w i + head)` >>
  qabbrev_tac `storage = (lookup_account c.msgParams.callee s.rollback.accounts).storage` >>
  qabbrev_tac `c1 = c with <|pc := 248; gasUsed := g1;
    stack := [lookup_storage slot storage; 76w*n2w i; slot; n2w i; cnt; head; tail]|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys1; msdomain := Collect d1|>` >>
  `run (s with contexts := (c,rb)::cs) = run (s1 with contexts := (c1,rb)::cs)` by
    simp[Abbr `c1`, Abbr `s1`, Abbr `storage`, Abbr `slot`] >>
  qabbrev_tac `off = 76*i` >>
  `76w * n2w i = (n2w off:bytes32)` by simp[Abbr `off`, wordsTheory.word_mul_n2w] >>
  `w2n (n2w off:bytes32) = off` by
    (simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def, Abbr `off`] >> decide_tac) >>
  qabbrev_tac `mx1 = word_size (off+32)*32` >>
  qabbrev_tac `cost1 = memory_expansion_cost (buffer_length c.memory) mx1` >>
  `cost1 <= 123` by
    (mp_tac (Q.INST [`p` |-> `off`, `b` |-> `c.memory`, `w` |-> `0w:bytes32`]
      queue_expanded_word_length) >>
     simp[LET_THM, Abbr `cost1`, Abbr `mx1`, Abbr `off`, Excl "buffer_length_write"] >>
     strip_tac >> gvs[]) >>
  `g1 + 12 + cost1 <= c.msgParams.gasLimit` by decide_tac >>
  qpat_x_assum `run (s with contexts := _) = _` (once_rewrite_tac o single) >>
  gs[Abbr `cost1`, Abbr `mx1`, Abbr `off`] >>
  simp[
    Q.INST [`w0` |-> `HD c.stack`, `off` |-> `EL 1 c.stack`,
      `ss` |-> `DROP 2 c.stack`,
      `mx` |-> `word_size (w2n (EL 1 c.stack)+32)*32`,
      `cost` |-> `memory_expansion_cost (buffer_length c.memory)
        (word_size (w2n (EL 1 c.stack)+32)*32)`] withdrawal_sender_run,
    Abbr `c1`, stack_limit_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  simp[Q.INST [`off` |-> `HD c.stack`, `slot` |-> `EL 1 c.stack`,
    `ss` |-> `DROP 2 c.stack`] withdrawal_pubkey_address_run, stack_limit_def] >>
  qmatch_goalsub_abbrev_tac `run (s1 with contexts := (c2,rb)::cs)` >>
  mp_tac (Q.INST [`c` |-> `c2`, `s` |-> `s1`, `d` |-> `d1`]
    (Q.INST [`key` |-> `HD c.stack`, `ss` |-> `TL c.stack`]
      system_sload_bounded_run)) >>
  (impl_tac >- (simp[Abbr `c2`, Abbr `s1`, GSYM withdrawal_instruction_def,
    withdrawal_sender_parse, stack_limit_def] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g2`, `keys2`, `d2`] strip_assume_tac) >>
  `buffer_length c2.memory <= 1280 /\ buffer_length c2.memory MOD 32 = 0` by
    (mp_tac (Q.INST [`p` |-> `76*i`, `b` |-> `c.memory`,
      `w` |-> `lookup_storage slot storage << 96`] queue_expanded_word_length) >>
     rewrite_tac[GSYM byteTheory.word_to_bytes_be_def,
       cv_stdTheory.word_to_bytes_be_eq_bytes_of_num, listTheory.REVERSE_REVERSE,
       GSYM cv_stdTheory.word_to_bytes_le_eq_bytes_of_num, byteTheory.word_to_bytes_le_def] >>
     simp[LET_THM, Abbr `c2`, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  `memory_expansion_cost (buffer_length c2.memory) (word_size (76*i+52)*32) <= 123` by
    (mp_tac (Q.INST [`p` |-> `76*i+20`, `b` |-> `c2.memory`,
      `w` |-> `0w:bytes32`] queue_expanded_word_length) >>
     simp[LET_THM, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `run (s1 with contexts := _) = _` (once_rewrite_tac o single) >>
  simp[Abbr `c2`, Abbr `s1`, vfmContextTheory.context_fupdcanon,
    wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w] >>
  qmatch_goalsub_abbrev_tac `c with <|stack := _; memory := m1; pc := _; gasUsed := _|>` >>
  gs[] >>
  simp[Q.INST [`w1` |-> `HD c.stack`, `off` |-> `EL 1 c.stack`,
    `slot` |-> `EL 2 c.stack`, `ss` |-> `DROP 3 c.stack`,
    `mx` |-> `word_size (w2n (EL 1 c.stack)+32)*32`,
    `cost` |-> `memory_expansion_cost (buffer_length c.memory)
      (word_size (w2n (EL 1 c.stack)+32)*32)`] withdrawal_pubkey_store_run,
    stack_limit_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  qmatch_goalsub_abbrev_tac `c with <|stack := _; memory := m2; pc := _; gasUsed := _|>` >>
  `buffer_length m2 <= 1280 /\ buffer_length m2 MOD 32 = 0` by
    (mp_tac (Q.INST [`p` |-> `76*i+20`, `b` |-> `m1`,
      `w` |-> `lookup_storage (slot+1w) storage`] queue_expanded_word_length) >>
     rewrite_tac[GSYM byteTheory.word_to_bytes_be_def,
       cv_stdTheory.word_to_bytes_be_eq_bytes_of_num, listTheory.REVERSE_REVERSE,
       GSYM cv_stdTheory.word_to_bytes_le_eq_bytes_of_num, byteTheory.word_to_bytes_le_def] >>
     simp[LET_THM, Abbr `m2`, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  `memory_expansion_cost (buffer_length m2) (word_size (76*i+84)*32) <= 123` by
    (mp_tac (Q.INST [`p` |-> `76*i+52`, `b` |-> `m2`,
      `w` |-> `0w:bytes32`] queue_expanded_word_length) >>
     simp[LET_THM, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  qmatch_goalsub_abbrev_tac `run (s2 with contexts := (c3,rb)::cs)` >>
  mp_tac (Q.INST [`c` |-> `c3`, `s` |-> `s2`, `d` |-> `d2`]
    (Q.INST [`key` |-> `HD c.stack`, `ss` |-> `TL c.stack`]
      system_sload_bounded_run)) >>
  (impl_tac >- (simp[Abbr `c3`, Abbr `s2`, GSYM withdrawal_instruction_def,
    withdrawal_pubkey_parse, stack_limit_def] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g3`, `keys3`, `d3`] strip_assume_tac) >>
  qpat_x_assum `run (s2 with contexts := _) = _` (once_rewrite_tac o single) >>
  simp[Abbr `c3`, Abbr `s2`, vfmContextTheory.context_fupdcanon,
    wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w] >>
  gs[] >>
  simp[Q.INST [`w2` |-> `HD c.stack`, `off` |-> `EL 1 c.stack`,
    `ss` |-> `DROP 2 c.stack`,
    `mx` |-> `word_size (w2n (EL 1 c.stack)+32)*32`,
    `cost` |-> `memory_expansion_cost (buffer_length c.memory)
      (word_size (w2n (EL 1 c.stack)+32)*32)`] withdrawal_pubkey_tail_run,
    stack_limit_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  qmatch_goalsub_abbrev_tac `c with <|stack := _; memory := m3; pc := _; gasUsed := _|>` >>
  simp[Q.INST [`w2` |-> `HD c.stack`, `off` |-> `EL 1 c.stack`,
    `ss` |-> `DROP 2 c.stack`] withdrawal_amount_address_run, stack_limit_def] >>
  `76*i+84 <= buffer_length m3 /\ buffer_length m3 <= 1280 /\
    buffer_length m3 MOD 32 = 0` by
    (mp_tac (Q.INST [`p` |-> `76*i+52`, `b` |-> `m2`,
      `w` |-> `(-1w:bytes32) << 128 && lookup_storage (slot+2w) storage`]
      queue_expanded_word_length) >>
     rewrite_tac[GSYM byteTheory.word_to_bytes_be_def,
       cv_stdTheory.word_to_bytes_be_eq_bytes_of_num, listTheory.REVERSE_REVERSE,
       GSYM cv_stdTheory.word_to_bytes_le_eq_bytes_of_num, byteTheory.word_to_bytes_le_def] >>
     simp[LET_THM, Abbr `m3`, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  simp[wordsTheory.word_add_n2w] >>
  qmatch_goalsub_abbrev_tac `run (s3 with contexts := (c4,rb)::cs)` >>
  mp_tac (Q.INST [`c` |-> `c4`, `s` |-> `s3`]
    (Q.INST [`p` |-> `w2n (HD c.stack)`, `v` |-> `EL 1 c.stack`,
      `idx` |-> `EL 2 c.stack`, `ss` |-> `DROP 3 c.stack`]
      withdrawal_amount_allocated_run)) >>
  (impl_tac >- (simp[Abbr `c4`, wordsTheory.w2n_n2w, wordsTheory.dimword_def,
     stack_limit_def] >> decide_tac)) >>
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  qpat_x_assum `run (s3 with contexts := _) = _` (once_rewrite_tac o single) >>
  gs[Abbr `c4`, Abbr `s3`, vfmContextTheory.context_fupdcanon,
    wordsTheory.w2n_n2w, wordsTheory.dimword_def,
    Excl "buffer_length_write", Excl "buffer_length_extend"] >>
  qmatch_goalsub_abbrev_tac `c with <|stack := _; memory := mf; pc := _; gasUsed := gf|>` >>
  qexistsl [`gf`, `keys3`, `d3`, `mf`] >>
  conj_tac >- (simp[Abbr `gf`] >> decide_tac) >>
  conj_tac >- simp[wordsTheory.word_add_n2w] >>
  reverse conj_tac >- (gvs[Excl "buffer_length_write", Excl "buffer_length_extend"] >> decide_tac) >>
  mp_tac (Q.INST [`b` |-> `c.memory`, `h` |-> `w2n (head:bytes32)`]
    withdrawal_expanded_record_memory) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  simp_tac pure_ss [LET_THM] >>
  disch_then (mp_tac o cj 9) >>
  simp_tac pure_ss [GSYM wordsTheory.word_add_n2w, GSYM wordsTheory.word_mul_n2w,
    wordsTheory.n2w_w2n] >>
  simp_tac pure_ss [wordsTheory.n2w_w2n, wordsTheory.LSR_ADD,
    wordsTheory.WORD_MULT_COMM, wordsTheory.WORD_ADD_ASSOC,
    wordsTheory.WORD_ADD_COMM, Abbr `slot`] >>
  simp_tac pure_ss [Abbr `mf`, Abbr `m3`, Abbr `m2`, Abbr `m1`] >>
  rewrite_tac[GSYM byteTheory.word_to_bytes_be_def,
    cv_stdTheory.word_to_bytes_be_eq_bytes_of_num, listTheory.REVERSE_REVERSE,
    GSYM cv_stdTheory.word_to_bytes_le_eq_bytes_of_num, byteTheory.word_to_bytes_le_def] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac std_ss [wordsTheory.WORD_MULT_COMM, wordsTheory.WORD_ADD_ASSOC,
    wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_AND_COMM,
    arithmeticTheory.ADD_COMM, arithmeticTheory.MULT_COMM,
    arithmeticTheory.LEFT_ADD_DISTRIB] >> simp[]
QED

Theorem withdrawal_loop_run[local]:
  c.pc = 225 /\ c.stack = [n2w i; n2w n; head; tail] /\
  c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  387 < LENGTH c.msgParams.code /\ s.msdomain = Collect d /\
  i <= n /\ n <= 16 /\
  76*i <= buffer_length c.memory /\ buffer_length c.memory <= 1280 /\
  buffer_length c.memory MOD 32 = 0 /\
  c.gasUsed + 7123*(n-i)+23 <= c.msgParams.gasLimit ==>
  ?g keys d' m. g <= c.gasUsed + 7123*(n-i)+23 /\
    run (s with contexts := (c,rb)::cs) = run (s with <|
      contexts := (c with <|pc := 387; stack := [n2w n; n2w n; head; tail];
        gasUsed := g; memory := m|>,rb)::cs;
      rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
      msdomain := Collect d'|>) /\
    buffer_take 0 (76*n) m = buffer_take 0 (76*i) c.memory ++
      FLAT (GENLIST (\j. read_withdrawal_request
        (lookup_account c.msgParams.callee s.rollback.accounts).storage
        (w2n head+i+j)) (n-i)) /\
    76*n <= buffer_length m /\ buffer_length m <= 1280 /\
    buffer_length m MOD 32 = 0
Proof
  map_every qid_spec_tac [`c`, `s`, `d`] >>
  measureInduct_on `n-i` >> rpt strip_tac >>
  Cases_on `i = n`
  >- (gvs[] >> drule_all withdrawal_loop_test_run >>
      disch_then (qspecl_then [`s`, `rb`, `cs`] mp_tac) >>
      strip_tac >>
      qexistsl [`c.gasUsed+23`, `s.rollback.accesses.storageKeys`, `d`, `c.memory`] >>
      simp[] >>
      qpat_x_assum `s.msdomain = _` (fn th => rewrite_tac[GSYM th]) >>
      simp[ vfmContextTheory.context_fupdcanon,
        vfmContextTheory.context_component_equality,
        vfmContextTheory.execution_state_component_equality] >>
      AP_TERM_TAC >> simp[vfmContextTheory.execution_state_component_equality,
        vfmContextTheory.context_component_equality]) >>
  `i < n /\ i < 16 /\ c.gasUsed+23 <= c.msgParams.gasLimit` by decide_tac >>
  `~((n2w i:bytes32) = n2w n)` by
    (simp[wordsTheory.n2w_11, wordsTheory.dimword_def] >> decide_tac) >>
  drule_all withdrawal_loop_test_run >>
  disch_then (qspecl_then [`s`, `rb`, `cs`] mp_tac) >> strip_tac >>
  qabbrev_tac `c1 = c with <|pc := 233; stack := [n2w i;n2w n;head;tail];
    gasUsed := c.gasUsed+23|>` >>
  `run (s with contexts := (c,rb)::cs) = run (s with contexts := (c1,rb)::cs)` by
    simp[Abbr `c1`] >>
  mp_tac (Q.INST [`c` |-> `c1`, `cnt` |-> `n2w n`] withdrawal_record_run) >>
  (impl_tac >- (simp[Abbr `c1`] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g1`, `keys1`, `d1`, `m1`] strip_assume_tac) >>
  qabbrev_tac `c2 = c1 with <|pc := 225; stack := [n2w (i+1);n2w n;head;tail];
    gasUsed := g1; memory := m1|>` >>
  qabbrev_tac `s2 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys1; msdomain := Collect d1|>` >>
  first_x_assum (qspec_then `i+1` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`d1`, `s2`, `c2`] mp_tac) >>
  (impl_tac >- (simp[Abbr `c2`, Abbr `s2`, Abbr `c1`] >>
    gvs[] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g2`, `keys2`, `d2`, `m2`] strip_assume_tac) >>
  qexistsl [`g2`, `keys2`, `d2`, `m2`] >>
  conj_tac >- (gvs[Abbr `c2`, Abbr `c1`] >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `run (s with contexts := (c,rb)::cs) = run (s with contexts := (c1,rb)::cs)`
        (once_rewrite_tac o single) >>
      qpat_x_assum `run (s with contexts := (c1,rb)::cs) = _`
        (once_rewrite_tac o single) >>
      qpat_x_assum `run (s2 with contexts := _) = _` (once_rewrite_tac o single) >>
      simp[Abbr `s2`, Abbr `c2`, Abbr `c1`, vfmContextTheory.context_fupdcanon,
        vfmContextTheory.execution_state_fupdcanon]) >>
  reverse conj_tac >- simp[] >>
  gvs[Abbr `c2`, Abbr `c1`, Abbr `s2`] >>
  `n-i = SUC (n-(i+1))` by decide_tac >>
  qpat_x_assum `n-i = _` (once_rewrite_tac o single) >>
  once_rewrite_tac[listTheory.GENLIST_CONS] >>
  simp_tac pure_ss [listTheory.FLAT, combinTheory.o_DEF,
    arithmeticTheory.ADD_CLAUSES] >>
  BETA_TAC >> simp_tac pure_ss [arithmeticTheory.ADD_CLAUSES] >>
  AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp_tac std_ss [FUN_EQ_THM] >> gen_tac >> AP_TERM_TAC >> decide_tac
QED

Theorem withdrawal_copy_run[local]:
  c.pc = 203 /\ c.stack = [] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  387 < LENGTH c.msgParams.code /\ s.msdomain = Collect d /\
  head = lookup_storage 2w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  tail = lookup_storage 3w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  w2n head <= w2n tail /\
  buffer_length c.memory <= 1280 /\ buffer_length c.memory MOD 32 = 0 /\
  c.gasUsed + 4246 + 7123 * MIN 16 (w2n tail-w2n head) + 23 <= c.msgParams.gasLimit ==>
  ?g keys d' m. g <= c.gasUsed + 4246 + 7123 * MIN 16 (w2n tail-w2n head) + 23 /\
    run (s with contexts := (c,rb)::cs) = run (s with <|
      contexts := (c with <|pc := 387;
        stack := [n2w (MIN 16 (w2n tail-w2n head));
                  n2w (MIN 16 (w2n tail-w2n head));head;tail];
        gasUsed := g; memory := m|>,rb)::cs;
      rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
      msdomain := Collect d'|>) /\
    buffer_take 0 (76 * MIN 16 (w2n tail-w2n head)) m =
      FLAT (GENLIST (\j. read_withdrawal_request
        (lookup_account c.msgParams.callee s.rollback.accounts).storage (w2n head+j))
        (MIN 16 (w2n tail-w2n head))) /\
    76 * MIN 16 (w2n tail-w2n head) <= buffer_length m /\
    buffer_length m <= 1280 /\ buffer_length m MOD 32 = 0
Proof
  strip_tac >>
  `c.gasUsed + 4246 <= c.msgParams.gasLimit` by decide_tac >>
  `223 < LENGTH c.msgParams.code` by decide_tac >>
  drule_all withdrawal_loop_entry_run >>
  disch_then (qspecl_then [`rb`, `cs`]
    (qx_choosel_then [`g1`, `keys1`, `d1`] strip_assume_tac)) >>
  qabbrev_tac `n = MIN 16 (w2n tail-w2n head)` >>
  qabbrev_tac `c1 = c with <|pc := 225; stack := [0w;n2w n;head;tail]; gasUsed := g1|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys1; msdomain := Collect d1|>` >>
  mp_tac (Q.INST [`c` |-> `c1`, `s` |-> `s1`, `i` |-> `0`, `d` |-> `d1`]
    withdrawal_loop_run) >>
  (impl_tac >- (simp[Abbr `c1`, Abbr `s1`, Abbr `n`] >> gvs[])) >>
  disch_then (qx_choosel_then [`g2`, `keys2`, `d2`, `m2`] strip_assume_tac) >>
  qexistsl [`g2`, `keys2`, `d2`, `m2`] >>
  conj_tac >- (gvs[Abbr `c1`] >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `run (s with contexts := _) = _` (once_rewrite_tac o single) >>
      qpat_x_assum `run (s1 with contexts := _) = _` (once_rewrite_tac o single) >>
      simp[Abbr `s1`, Abbr `c1`, vfmContextTheory.context_fupdcanon,
        vfmContextTheory.execution_state_fupdcanon]) >>
  gvs[Abbr `s1`, Abbr `c1`] >> simp[vfmBufferTheory.buffer_take_to_list]
QED

Definition consolidation_instruction_def:
  consolidation_instruction pc = FLOOKUP (parse_code 0 FEMPTY consolidation_request_code) pc
End
val () = cv_auto_trans consolidation_instruction_def;

Theorem consolidation_entry_parse[local]:
  consolidation_instruction 211 = SOME JumpDest /\
  consolidation_instruction 212 = SOME (Push 1 [3w]) /\
  consolidation_instruction 214 = SOME SLoad /\
  consolidation_instruction 215 = SOME (Push 1 [2w]) /\
  consolidation_instruction 217 = SOME SLoad /\
  consolidation_instruction 218 = SOME (Dup 0) /\
  consolidation_instruction 219 = SOME (Dup 2) /\
  consolidation_instruction 220 = SOME Sub /\
  consolidation_instruction 221 = SOME (Dup 0) /\
  consolidation_instruction 222 = SOME (Push 1 [2w]) /\
  consolidation_instruction 224 = SOME GT /\
  consolidation_instruction 225 = SOME (Push 1 [231w]) /\
  consolidation_instruction 227 = SOME JumpI /\
  consolidation_instruction 228 = SOME Pop /\
  consolidation_instruction 229 = SOME (Push 1 [2w]) /\
  consolidation_instruction 231 = SOME JumpDest /\
  consolidation_instruction 232 = SOME (Push 0 []) /\
  consolidation_instruction 233 = SOME JumpDest /\
  consolidation_instruction 234 = SOME (Dup 1) /\
  consolidation_instruction 235 = SOME (Dup 1) /\
  consolidation_instruction 236 = SOME Eq /\
  consolidation_instruction 237 = SOME (Push 2 [1w; 41w]) /\
  consolidation_instruction 240 = SOME JumpI /\
  consolidation_instruction 297 = SOME JumpDest
Proof
  rpt conj_tac >> CONV_TAC cv_eval
QED

Theorem consolidation_heads_run[local]:
  c.pc = 211 /\ c.stack = [] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  s.msdomain = Collect d /\ c.gasUsed + 4207 <= c.msgParams.gasLimit ==>
  ?g keys d'. g <= c.gasUsed + 4207 /\
  run (s with contexts := (c, rb)::cs) = run (s with <|
    contexts := (c with <|pc := 218;
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
     simp[GSYM consolidation_instruction_def, consolidation_entry_parse]) >>
  mp_tac (Q.INST [`c` |-> `c1`, `slot` |-> `3w:byte`] system_push1_sload_run) >>
  (impl_tac >- simp[Abbr `c1`, GSYM consolidation_instruction_def,
    consolidation_entry_parse, stack_limit_def]) >>
  simp[Abbr `c1`] >>
  disch_then (qx_choose_then `g1` (qx_choose_then `keys1` (qx_choose_then `d1` strip_assume_tac))) >>
  qabbrev_tac `c2 = c with <|pc := 215;
    stack := [lookup_storage 3w (lookup_account c.msgParams.callee s.rollback.accounts).storage];
    gasUsed := g1|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys1; msdomain := Collect d1|>` >>
  mp_tac (Q.INST [`c` |-> `c2`, `s` |-> `s1`, `d` |-> `d1`,
    `slot` |-> `2w:byte`] system_push1_sload_run) >>
  (impl_tac >- simp[Abbr `c2`, Abbr `s1`, GSYM consolidation_instruction_def,
    consolidation_entry_parse, stack_limit_def]) >>
  simp[Abbr `c2`, Abbr `s1`] >>
  disch_then (qx_choose_then `g2` (qx_choose_then `keys2` (qx_choose_then `d2` strip_assume_tac))) >>
  qexistsl [`g2`, `keys2`, `d2`] >>
  conj_tac >- decide_tac >> simp[]
QED

Theorem consolidation_count_test_run[local]:
  c.pc = 218 /\ c.stack = [head; tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  c.gasUsed + 18 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := [b2w (w2n (tail - head) < 2); tail - head; head; tail];
      gasUsed := c.gasUsed + 18; pc := 225|>, rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [2w:byte] = (2w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Sub`, `f` |-> `word_sub:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[2w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `GT`,
    `f` |-> `(\x y:bytes32. b2w (w2n x > w2n y))`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  `-1w * head + tail = tail - head` by wordsLib.WORD_DECIDE_TAC >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac [arithmeticTheory.GREATER_DEF,
    vfmContextTheory.context_fupdcanon] >> REFL_TAC
QED

Theorem consolidation_count_select_run[local]:
  c.pc = 225 /\ c.stack = [b2w (w2n cnt < 2); cnt; head; tail] /\
  c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  231 < LENGTH c.msgParams.code /\
  c.gasUsed + 21 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := [0w; if w2n cnt < 2 then cnt else 2w; head; tail];
      gasUsed := c.gasUsed + (if w2n cnt < 2 then 16 else 21);
      pc := 233|>, rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [231w:byte] = (231w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  `word_of_bytes F 0w [2w:byte] = (2w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[231w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  Cases_on `w2n cnt < 2` >>
  simp[SimpLHS, system_jumpi_run, b2w_def, wordsTheory.dimword_def,
    GSYM consolidation_instruction_def, consolidation_entry_parse] >> simp[] >>
  simp[SimpLHS, system_pop_run,
    Q.INST [`n` |-> `1`, `ws` |-> `[2w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, system_jumpdest_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`, `ws` |-> `[]:byte list`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def,
    static_gas_def, opcode_def, byteTheory.word_of_bytes_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem consolidation_count_run[local]:
  c.pc = 218 /\ c.stack = [head; tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  231 < LENGTH c.msgParams.code /\ w2n head <= w2n tail /\
  c.gasUsed + 39 <= c.msgParams.gasLimit ==>
  ?g. g <= c.gasUsed + 39 /\
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := [0w; n2w (MIN 2 (w2n tail - w2n head)); head; tail];
      gasUsed := g; pc := 233|>, rb)::cs)
Proof
  strip_tac >>
  `w2n (tail - head) = w2n tail - w2n head` by
    (irule wordsTheory.word_sub_w2n >> simp[wordsTheory.WORD_LS]) >>
  qexists_tac `c.gasUsed + 18 + (if w2n (tail - head) < 2 then 16 else 21)` >>
  conj_tac >- (IF_CASES_TAC >> decide_tac) >>
  `c.gasUsed + 18 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all consolidation_count_test_run >>
  disch_then (fn th => once_rewrite_tac [th]) >>
  mp_tac (Q.INST [`c` |-> `c with <|
    stack := [b2w (w2n (tail - head) < 2); tail - head; head; tail];
    gasUsed := c.gasUsed + 18; pc := 225|>`, `cnt` |-> `tail - head`]
    consolidation_count_select_run) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => once_rewrite_tac [th]) >>
  `n2w (w2n tail - w2n head) = tail - head` by
    metis_tac[wordsTheory.n2w_w2n] >>
  `(if w2n (tail - head) < 2 then tail - head else 2w) =
    (n2w (MIN 2 (w2n tail - w2n head)):bytes32)` by
    (Cases_on `w2n (tail - head) < 2` >> simp[arithmeticTheory.MIN_DEF]) >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem consolidation_loop_entry_run[local]:
  c.pc = 211 /\ c.stack = [] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  231 < LENGTH c.msgParams.code /\ s.msdomain = Collect d /\
  head = lookup_storage 2w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  tail = lookup_storage 3w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  w2n head <= w2n tail /\ c.gasUsed + 4246 <= c.msgParams.gasLimit ==>
  ?g keys d'. g <= c.gasUsed + 4246 /\
  run (s with contexts := (c, rb)::cs) = run (s with <|
    contexts := (c with <|pc := 233;
      stack := [0w; n2w (MIN 2 (w2n tail - w2n head)); head; tail];
      gasUsed := g|>, rb)::cs;
    rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `c.gasUsed + 4207 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all consolidation_heads_run >>
  disch_then (qspecl_then [`rb`, `cs`] strip_assume_tac) >>
  qabbrev_tac `c1 = c with <|pc := 218; stack := [head; tail]; gasUsed := g|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys; msdomain := Collect d'|>` >>
  mp_tac (Q.INST [`c` |-> `c1`, `s` |-> `s1`] consolidation_count_run) >>
  (impl_tac >- simp[Abbr `c1`]) >>
  disch_then (qx_choose_then `g2` strip_assume_tac) >>
  qexistsl [`g2`, `keys`, `d'`] >>
  conj_tac >- gvs[Abbr `c1`] >>
  gvs[Abbr `c1`, Abbr `s1`]
QED

Theorem consolidation_copy_parse[local]:
  consolidation_instruction 241 = SOME (Dup 2) /\
  consolidation_instruction 242 = SOME (Dup 1) /\
  consolidation_instruction 243 = SOME Add /\
  consolidation_instruction 244 = SOME (Push 1 [4w]) /\
  consolidation_instruction 246 = SOME Mul /\
  consolidation_instruction 247 = SOME (Push 1 [4w]) /\
  consolidation_instruction 249 = SOME Add /\
  consolidation_instruction 250 = SOME (Dup 1) /\
  consolidation_instruction 251 = SOME (Push 1 [116w]) /\
  consolidation_instruction 253 = SOME Mul /\
  consolidation_instruction 254 = SOME (Dup 1) /\
  consolidation_instruction 255 = SOME SLoad /\
  consolidation_instruction 256 = SOME (Push 1 [96w]) /\
  consolidation_instruction 258 = SOME ShL /\
  consolidation_instruction 259 = SOME (Dup 1) /\
  consolidation_instruction 260 = SOME MStore /\
  consolidation_instruction 261 = SOME (Push 1 [20w]) /\
  consolidation_instruction 263 = SOME Add /\
  consolidation_instruction 264 = SOME (Dup 1) /\
  consolidation_instruction 265 = SOME (Push 1 [1w]) /\
  consolidation_instruction 267 = SOME Add /\
  consolidation_instruction 268 = SOME SLoad /\
  consolidation_instruction 269 = SOME (Dup 1) /\
  consolidation_instruction 270 = SOME MStore /\
  consolidation_instruction 271 = SOME (Push 1 [32w]) /\
  consolidation_instruction 273 = SOME Add /\
  consolidation_instruction 274 = SOME (Dup 1) /\
  consolidation_instruction 275 = SOME (Push 1 [2w]) /\
  consolidation_instruction 277 = SOME Add /\
  consolidation_instruction 278 = SOME SLoad /\
  consolidation_instruction 279 = SOME (Dup 1) /\
  consolidation_instruction 280 = SOME MStore /\
  consolidation_instruction 281 = SOME (Push 1 [32w]) /\
  consolidation_instruction 283 = SOME Add /\
  consolidation_instruction 284 = SOME (Swap 0) /\
  consolidation_instruction 285 = SOME (Push 1 [3w]) /\
  consolidation_instruction 287 = SOME Add /\
  consolidation_instruction 288 = SOME SLoad /\
  consolidation_instruction 289 = SOME (Swap 0) /\
  consolidation_instruction 290 = SOME MStore /\
  consolidation_instruction 291 = SOME (Push 1 [1w]) /\
  consolidation_instruction 293 = SOME Add /\
  consolidation_instruction 294 = SOME (Push 1 [233w]) /\
  consolidation_instruction 296 = SOME Jump
Proof
  rpt conj_tac >> CONV_TAC cv_eval
QED

Theorem consolidation_loop_test_run[local]:
  c.pc = 233 /\ c.stack = [idx; cnt; head; tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  297 < LENGTH c.msgParams.code /\
  c.gasUsed + 23 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := [idx; cnt; head; tail]; gasUsed := c.gasUsed + 23;
      pc := if idx = cnt then 297 else 241|>, rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [41w:byte; 1w] = (297w:bytes32)` by
    (simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero,
      byteTheory.word_slice_alt_def] >> wordsLib.WORD_DECIDE_TAC) >>
  simp[SimpLHS, system_jumpdest_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Eq`,
    `f` |-> `(\x y:bytes32. b2w (x = y))`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`, `ws` |-> `[1w:byte; 41w]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_entry_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  Cases_on `idx = cnt` >>
  simp[SimpLHS, system_jumpi_run, b2w_def, wordsTheory.dimword_def,
    GSYM consolidation_instruction_def, consolidation_entry_parse] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem consolidation_copy_address_run[local]:
  c.pc = 241 /\ c.stack = [idx; cnt; head; tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  c.gasUsed + 37 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := [4w + 4w * (idx + head); 116w * idx;
      4w + 4w * (idx + head); idx; cnt; head; tail];
      gasUsed := c.gasUsed + 37; pc := 255|>, rb)::cs)
Proof
  strip_tac >>
  `!b:byte. word_of_bytes F 0w [b] = (w2w b:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[4w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Mul`,
    `f` |-> `word_mul:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[4w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[116w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Mul`,
    `f` |-> `word_mul:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem consolidation_copy_first_load_run[local]:
  c.pc = 241 /\ c.stack = [idx; cnt; head; tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  s.msdomain = Collect d /\ c.gasUsed + 2137 <= c.msgParams.gasLimit ==>
  ?g keys d'. g <= c.gasUsed + 2137 /\
  run (s with contexts := (c, rb)::cs) = run (s with <|
    contexts := (c with <|pc := 256; gasUsed := g;
      stack := [lookup_storage (4w + 4w * (idx + head))
        (lookup_account c.msgParams.callee s.rollback.accounts).storage;
        116w * idx; 4w + 4w * (idx + head); idx; cnt; head; tail]|>, rb)::cs;
    rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `c.gasUsed + 37 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all consolidation_copy_address_run >> disch_then (once_rewrite_tac o single) >>
  qabbrev_tac `slot = 4w + 4w * (idx + head)` >>
  mp_tac (Q.INST [
    `c` |-> `c with <|stack := [slot; 116w * idx; slot; idx; cnt; head; tail];
      gasUsed := c.gasUsed + 37; pc := 255|>`,
    `key` |-> `slot:bytes32`, `ss` |-> `[116w * idx; slot; idx; cnt; head; tail]`]
    system_sload_bounded_run) >>
  (impl_tac >- simp[GSYM consolidation_instruction_def,
    consolidation_copy_parse, stack_limit_def]) >>
  simp[vfmContextTheory.context_fupdcanon, Abbr `slot`] >>
  strip_tac >> qexistsl [`g`, `keys`, `d'`] >> simp[]
QED

Theorem consolidation_sender_run[local]:
  c.pc = 256 /\ c.stack = w0::off::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 3 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  mx = word_size (w2n off + 32) * 32 /\
  cost = memory_expansion_cost (buffer_length c.memory) mx /\
  c.gasUsed + 12 + cost <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := off::ss; pc := 261; gasUsed := c.gasUsed + 12 + cost;
      memory := buffer_write (w2n off) (REVERSE (word_to_bytes (w0 << 96) F))
        (buffer_extend (MAX (buffer_length c.memory) mx - buffer_length c.memory) c.memory)|>, rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [96w:byte] = (96w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[96w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `ShL`,
    `f` |-> `(\n w:bytes32. w << w2n n)`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def] >>
  gvs[] >>
  mp_tac (Q.INST [`op` |-> `MStore`,
    `c` |-> `c with <|stack := off::(w0 << 96)::off::ss; pc := 260; gasUsed := c.gasUsed + 9|>`]
    (SRULE [LET_THM] system_mstore_run)) >>
  (impl_tac >- simp[GSYM consolidation_instruction_def, consolidation_copy_parse]) >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem consolidation_pubkey_address_run[local]:
  c.pc = 261 /\ c.stack = off::slot::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 3 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  c.gasUsed + 15 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := (1w + slot)::(20w + off)::slot::ss;
      pc := 268; gasUsed := c.gasUsed + 15|>, rb)::cs)
Proof
  strip_tac >>
  `!b:byte. word_of_bytes F 0w [b] = (w2w b:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[20w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[1w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem consolidation_pubkey_store_run[local]:
  (c.pc = 269 \/ c.pc = 279) /\ c.stack = w::off::slot::ss /\
  c.jumpDest = NONE /\ LENGTH ss + 3 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  mx = word_size (w2n off + 32)*32 /\
  cost = memory_expansion_cost (buffer_length c.memory) mx /\
  c.gasUsed + 6 + cost <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|stack := off::slot::ss; pc := c.pc+2;
      gasUsed := c.gasUsed+6+cost;
      memory := buffer_write (w2n off) (REVERSE (word_to_bytes w F))
        (buffer_extend (MAX (buffer_length c.memory) mx - buffer_length c.memory) c.memory)|>,rb)::cs)
Proof
  strip_tac >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def] >>
  gvs[] >>
  mp_tac (Q.INST [`op` |-> `MStore`,
    `c` |-> `c with <|stack := off::w::off::slot::ss;
      pc := c.pc+1; gasUsed := c.gasUsed+3|>`]
    (SRULE [LET_THM] system_mstore_run)) >>
  (impl_tac >- simp[GSYM consolidation_instruction_def, consolidation_copy_parse]) >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem consolidation_second_address_run[local]:
  c.pc = 271 /\ c.stack = off::slot::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 3 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  c.gasUsed + 15 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := (2w + slot)::(32w + off)::slot::ss;
      pc := 278; gasUsed := c.gasUsed + 15|>, rb)::cs)
Proof
  strip_tac >>
  `!b:byte. word_of_bytes F 0w [b] = (w2w b:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[32w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_dup_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[2w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem consolidation_third_address_run[local]:
  c.pc = 281 /\ c.stack = off::slot::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 2 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  c.gasUsed + 15 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c, rb)::cs) = run (s with contexts :=
    (c with <|stack := (3w + slot)::(32w + off)::ss;
      pc := 288; gasUsed := c.gasUsed + 15|>, rb)::cs)
Proof
  strip_tac >>
  `!b:byte. word_of_bytes F 0w [b] = (w2w b:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[32w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_swap_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[3w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem consolidation_final_store_run[local]:
  c.pc = 289 /\ c.stack = w::off::ss /\
  c.jumpDest = NONE /\ LENGTH ss + 2 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  mx = word_size (w2n off + 32)*32 /\
  cost = memory_expansion_cost (buffer_length c.memory) mx /\
  c.gasUsed + 6 + cost <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|stack := ss; pc := 291;
      gasUsed := c.gasUsed+6+cost;
      memory := buffer_write (w2n off) (REVERSE (word_to_bytes w F))
        (buffer_extend (MAX (buffer_length c.memory) mx - buffer_length c.memory) c.memory)|>,rb)::cs)
Proof
  strip_tac >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_swap_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def] >>
  gvs[] >>
  mp_tac (Q.INST [`op` |-> `MStore`,
    `c` |-> `c with <|stack := off::w::ss;
      pc := 290; gasUsed := c.gasUsed+3|>`]
    (SRULE [LET_THM] system_mstore_run)) >>
  (impl_tac >- simp[GSYM consolidation_instruction_def, consolidation_copy_parse]) >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem consolidation_backedge_run[local]:
  c.pc = 291 /\ c.stack = idx::ss /\ c.jumpDest = NONE /\
  LENGTH ss + 2 < stack_limit /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  233 < LENGTH c.msgParams.code /\
  c.gasUsed + 17 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|stack := (1w+idx)::ss; pc := 233; gasUsed := c.gasUsed+17|>,rb)::cs)
Proof
  strip_tac >>
  `!b:byte. word_of_bytes F 0w [b] = (w2w b:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[1w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`,
    `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[233w:byte]`] system_push_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, system_jump_run,
    GSYM consolidation_instruction_def, consolidation_copy_parse, consolidation_entry_parse] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem consolidation_expanded_record_memory[local]:
  i < 2 /\ 116*i <= buffer_length b /\ buffer_length b <= 1280 /\
  buffer_length b MOD 32 = 0 ==>
  let off = 116*i in
  let base = 4 + (h+i)*4 in
  let w0 = lookup_storage (n2w base) storage in
  let w1 = lookup_storage (n2w (base+1)) storage in
  let w2 = lookup_storage (n2w (base+2)) storage in
  let w3 = lookup_storage (n2w (base+3)) storage in
  let mx1 = word_size (off+32)*32 in
  let m1 = buffer_write off (word_to_bytes (w0 << 96) T)
    (buffer_extend (MAX (buffer_length b) mx1 - buffer_length b) b) in
  let mx2 = word_size (off+52)*32 in
  let m2 = buffer_write (off+20) (word_to_bytes w1 T)
    (buffer_extend (MAX (buffer_length m1) mx2 - buffer_length m1) m1) in
  let mx3 = word_size (off+84)*32 in
  let m3 = buffer_write (off+52) (word_to_bytes w2 T)
    (buffer_extend (MAX (buffer_length m2) mx3 - buffer_length m2) m2) in
  let mx4 = word_size (off+116)*32 in
  let m4 = buffer_write (off+84) (word_to_bytes w3 T)
    (buffer_extend (MAX (buffer_length m3) mx4 - buffer_length m3) m3) in
  memory_expansion_cost (buffer_length b) mx1 <= 123 /\
  memory_expansion_cost (buffer_length m1) mx2 <= 123 /\
  memory_expansion_cost (buffer_length m2) mx3 <= 123 /\
  memory_expansion_cost (buffer_length m3) mx4 <= 123 /\
  off+116 <= buffer_length m4 /\ buffer_length m4 <= 1280 /\
  buffer_length m4 MOD 32 = 0 /\
  buffer_take 0 (off+116) m4 =
    buffer_take 0 off b ++ read_consolidation_request storage (h+i)
Proof
  strip_tac >> rpt BasicProvers.LET_ELIM_TAC >>
  `off + 116 <= 1280` by (simp[Abbr `off`] >> decide_tac) >>
  `buffer_length m1 <= 1280 /\ buffer_length m1 MOD 32 = 0 /\
   memory_expansion_cost (buffer_length b) mx1 <= 123` by
    (mp_tac (Q.INST [`p` |-> `off`, `w` |-> `w0 << 96`]
      queue_expanded_word_length) >>
     simp[Abbr `m1`, Abbr `mx1`, LET_THM,
       Excl "buffer_length_write", Excl "buffer_length_extend"] >> strip_tac >> gvs[]) >>
  `buffer_length m2 <= 1280 /\ buffer_length m2 MOD 32 = 0 /\
   memory_expansion_cost (buffer_length m1) mx2 <= 123` by
    (mp_tac (Q.INST [`p` |-> `off+20`, `w` |-> `w1`, `b` |-> `m1`]
      queue_expanded_word_length) >>
     simp[Abbr `m2`, Abbr `mx2`, LET_THM,
       Excl "buffer_length_write", Excl "buffer_length_extend"] >> strip_tac >> gvs[]) >>
  `buffer_length m3 <= 1280 /\ buffer_length m3 MOD 32 = 0 /\
   memory_expansion_cost (buffer_length m2) mx3 <= 123` by
    (mp_tac (Q.INST [`p` |-> `off+52`, `w` |-> `w2`, `b` |-> `m2`]
      queue_expanded_word_length) >>
     simp[Abbr `m3`, Abbr `mx3`, LET_THM,
       Excl "buffer_length_write", Excl "buffer_length_extend"] >> strip_tac >> gvs[]) >>
  `off+116 <= buffer_length m4 /\ buffer_length m4 <= 1280 /\
   buffer_length m4 MOD 32 = 0 /\
   memory_expansion_cost (buffer_length m3) mx4 <= 123` by
    (mp_tac (Q.INST [`p` |-> `off+84`, `w` |-> `w3`, `b` |-> `m3`]
      queue_expanded_word_length) >>
     simp[Abbr `m4`, Abbr `mx4`, LET_THM,
       Excl "buffer_length_write", Excl "buffer_length_extend"] >> strip_tac >> gvs[]) >>
  simp[Excl "buffer_length_write"] >>
  mp_tac (Q.INST [`idx` |-> `h+i`] consolidation_record_memory) >>
  (impl_tac >- simp[]) >> simp_tac pure_ss [LET_THM] >>
  disch_then (fn th => once_rewrite_tac[GSYM th]) >>
  irule queue_take_read_cong >> conj_tac
  >- (rpt gen_tac >>
      simp_tac (srw_ss()) [Abbr `m4`, Abbr `m3`, Abbr `m2`,
        Abbr `m1`, Abbr `w0`, Abbr `w1`, Abbr `w2`, Abbr `w3`, Abbr `base'`,
        queue_read_write_extend] >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      rpt (irule queue_read_write_cong >> rpt gen_tac >>
        simp_tac pure_ss [queue_read_write_extend]) >> simp[]) >>
  conj_tac >- simp[Excl "buffer_length_write"] >>
  irule vfmBufferTheory.buffer_write_covers_endpoint >>
  simp[byteTheory.LENGTH_word_to_bytes, Excl "buffer_length_write"] >>
  pure_once_rewrite_tac[GSYM listTheory.LENGTH_NIL] >>
  pure_rewrite_tac[byteTheory.LENGTH_word_to_bytes] >> simp[]
QED

Theorem consolidation_record_run[local]:
  c.pc = 241 /\ c.stack = [n2w i; cnt; head; tail] /\
  c.jumpDest = NONE /\ i < 2 /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  233 < LENGTH c.msgParams.code /\ s.msdomain = Collect d /\
  116*i <= buffer_length c.memory /\ buffer_length c.memory <= 1280 /\
  buffer_length c.memory MOD 32 = 0 /\
  c.gasUsed + 9500 <= c.msgParams.gasLimit ==>
  ?g keys d' m. g <= c.gasUsed + 9500 /\
    run (s with contexts := (c, rb)::cs) = run (s with <|
      contexts := (c with <|pc := 233; stack := [n2w (i+1); cnt; head; tail];
        gasUsed := g; memory := m|>, rb)::cs;
      rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
      msdomain := Collect d'|>) /\
    buffer_take 0 (116*(i+1)) m = buffer_take 0 (116*i) c.memory ++
      read_consolidation_request
        (lookup_account c.msgParams.callee s.rollback.accounts).storage (w2n head+i) /\
    116*(i+1) <= buffer_length m /\ buffer_length m <= 1280 /\
    buffer_length m MOD 32 = 0
Proof
  strip_tac >>
  `c.gasUsed + 2137 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all consolidation_copy_first_load_run >>
  disch_then (qspecl_then [`rb`, `cs`]
    (qx_choosel_then [`g1`, `keys1`, `d1`] strip_assume_tac)) >>
  qabbrev_tac `slot = 4w + 4w * (n2w i + head)` >>
  qabbrev_tac `storage = (lookup_account c.msgParams.callee s.rollback.accounts).storage` >>
  qabbrev_tac `c1 = c with <|pc := 256; gasUsed := g1;
    stack := [lookup_storage slot storage; 116w*n2w i; slot; n2w i; cnt; head; tail]|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys1; msdomain := Collect d1|>` >>
  `run (s with contexts := (c,rb)::cs) = run (s1 with contexts := (c1,rb)::cs)` by
    simp[Abbr `c1`, Abbr `s1`, Abbr `storage`, Abbr `slot`] >>
  qabbrev_tac `off = 116*i` >>
  `116w * n2w i = (n2w off:bytes32)` by simp[Abbr `off`, wordsTheory.word_mul_n2w] >>
  `w2n (n2w off:bytes32) = off` by
    (simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def, Abbr `off`] >> decide_tac) >>
  qabbrev_tac `mx1 = word_size (off+32)*32` >>
  qabbrev_tac `cost1 = memory_expansion_cost (buffer_length c.memory) mx1` >>
  `cost1 <= 123` by
    (mp_tac (Q.INST [`p` |-> `off`, `b` |-> `c.memory`, `w` |-> `0w:bytes32`]
      queue_expanded_word_length) >>
     simp[LET_THM, Abbr `cost1`, Abbr `mx1`, Abbr `off`, Excl "buffer_length_write"] >>
     strip_tac >> gvs[]) >>
  `g1 + 12 + cost1 <= c.msgParams.gasLimit` by decide_tac >>
  qpat_x_assum `run (s with contexts := _) = _` (once_rewrite_tac o single) >>
  gs[Abbr `cost1`, Abbr `mx1`, Abbr `off`] >>
  simp[Q.INST [`w0` |-> `HD c.stack`, `off` |-> `EL 1 c.stack`,
    `ss` |-> `DROP 2 c.stack`,
    `mx` |-> `word_size (w2n (EL 1 c.stack)+32)*32`,
    `cost` |-> `memory_expansion_cost (buffer_length c.memory)
      (word_size (w2n (EL 1 c.stack)+32)*32)`] consolidation_sender_run,
    Abbr `c1`, stack_limit_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  simp[Q.INST [`off` |-> `HD c.stack`, `slot` |-> `EL 1 c.stack`,
    `ss` |-> `DROP 2 c.stack`] consolidation_pubkey_address_run, stack_limit_def] >>
  qmatch_goalsub_abbrev_tac `run (s1 with contexts := (c2,rb)::cs)` >>
  mp_tac (Q.INST [`c` |-> `c2`, `s` |-> `s1`, `d` |-> `d1`]
    (Q.INST [`key` |-> `HD c.stack`, `ss` |-> `TL c.stack`]
      system_sload_bounded_run)) >>
  (impl_tac >- (simp[Abbr `c2`, Abbr `s1`, GSYM consolidation_instruction_def,
    consolidation_copy_parse, stack_limit_def] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g2`, `keys2`, `d2`] strip_assume_tac) >>
  `buffer_length c2.memory <= 1280 /\ buffer_length c2.memory MOD 32 = 0` by
    (mp_tac (Q.INST [`p` |-> `116*i`, `b` |-> `c.memory`,
      `w` |-> `lookup_storage slot storage << 96`] queue_expanded_word_length) >>
     rewrite_tac[GSYM byteTheory.word_to_bytes_be_def,
       cv_stdTheory.word_to_bytes_be_eq_bytes_of_num, listTheory.REVERSE_REVERSE,
       GSYM cv_stdTheory.word_to_bytes_le_eq_bytes_of_num, byteTheory.word_to_bytes_le_def] >>
     simp[LET_THM, Abbr `c2`, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  `memory_expansion_cost (buffer_length c2.memory) (word_size (116*i+52)*32) <= 123` by
    (mp_tac (Q.INST [`p` |-> `116*i+20`, `b` |-> `c2.memory`,
      `w` |-> `0w:bytes32`] queue_expanded_word_length) >>
     simp[LET_THM, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `run (s1 with contexts := _) = _` (once_rewrite_tac o single) >>
  simp[Abbr `c2`, Abbr `s1`, vfmContextTheory.context_fupdcanon,
    wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w] >>
  qmatch_goalsub_abbrev_tac `c with <|stack := _; memory := m1; pc := _; gasUsed := _|>` >>
  gs[] >>
  simp[Q.INST [`w` |-> `HD c.stack`, `off` |-> `EL 1 c.stack`,
    `slot` |-> `EL 2 c.stack`, `ss` |-> `DROP 3 c.stack`,
    `mx` |-> `word_size (w2n (EL 1 c.stack)+32)*32`,
    `cost` |-> `memory_expansion_cost (buffer_length c.memory)
      (word_size (w2n (EL 1 c.stack)+32)*32)`] consolidation_pubkey_store_run,
    stack_limit_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  qmatch_goalsub_abbrev_tac `c with <|stack := _; memory := m2; pc := _; gasUsed := _|>` >>
  `buffer_length m2 <= 1280 /\ buffer_length m2 MOD 32 = 0` by
    (mp_tac (Q.INST [`p` |-> `116*i+20`, `b` |-> `m1`,
      `w` |-> `lookup_storage (slot+1w) storage`] queue_expanded_word_length) >>
     rewrite_tac[GSYM byteTheory.word_to_bytes_be_def,
       cv_stdTheory.word_to_bytes_be_eq_bytes_of_num, listTheory.REVERSE_REVERSE,
       GSYM cv_stdTheory.word_to_bytes_le_eq_bytes_of_num, byteTheory.word_to_bytes_le_def] >>
     simp[LET_THM, Abbr `m2`, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  `memory_expansion_cost (buffer_length m2) (word_size (116*i+84)*32) <= 123` by
    (mp_tac (Q.INST [`p` |-> `116*i+52`, `b` |-> `m2`,
      `w` |-> `0w:bytes32`] queue_expanded_word_length) >>
     simp[LET_THM, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  simp[Q.INST [`off` |-> `HD c.stack`, `slot` |-> `EL 1 c.stack`,
    `ss` |-> `DROP 2 c.stack`] consolidation_second_address_run, stack_limit_def] >>
  qmatch_goalsub_abbrev_tac `run (s2 with contexts := (c3,rb)::cs)` >>
  mp_tac (Q.INST [`c` |-> `c3`, `s` |-> `s2`, `d` |-> `d2`]
    (Q.INST [`key` |-> `HD c.stack`, `ss` |-> `TL c.stack`]
      system_sload_bounded_run)) >>
  (impl_tac >- (simp[Abbr `c3`, Abbr `s2`, GSYM consolidation_instruction_def,
    consolidation_copy_parse, stack_limit_def] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g3`, `keys3`, `d3`] strip_assume_tac) >>
  qpat_x_assum `run (s2 with contexts := _) = _` (once_rewrite_tac o single) >>
  simp[Abbr `c3`, Abbr `s2`, vfmContextTheory.context_fupdcanon,
    wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w] >> gs[] >>
  simp[Q.INST [`w` |-> `HD c.stack`, `off` |-> `EL 1 c.stack`,
    `slot` |-> `EL 2 c.stack`, `ss` |-> `DROP 3 c.stack`,
    `mx` |-> `word_size (w2n (EL 1 c.stack)+32)*32`,
    `cost` |-> `memory_expansion_cost (buffer_length c.memory)
      (word_size (w2n (EL 1 c.stack)+32)*32)`] consolidation_pubkey_store_run,
    stack_limit_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  qmatch_goalsub_abbrev_tac `c with <|stack := _; memory := m3; pc := _; gasUsed := _|>` >>
  `buffer_length m3 <= 1280 /\ buffer_length m3 MOD 32 = 0` by
    (mp_tac (Q.INST [`p` |-> `116*i+52`, `b` |-> `m2`,
      `w` |-> `lookup_storage (slot+2w) storage`] queue_expanded_word_length) >>
     rewrite_tac[GSYM byteTheory.word_to_bytes_be_def,
       cv_stdTheory.word_to_bytes_be_eq_bytes_of_num, listTheory.REVERSE_REVERSE,
       GSYM cv_stdTheory.word_to_bytes_le_eq_bytes_of_num, byteTheory.word_to_bytes_le_def] >>
     simp[LET_THM, Abbr `m3`, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  `memory_expansion_cost (buffer_length m3) (word_size (116*i+116)*32) <= 123` by
    (mp_tac (Q.INST [`p` |-> `116*i+84`, `b` |-> `m3`,
      `w` |-> `0w:bytes32`] queue_expanded_word_length) >>
     simp[LET_THM, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  simp[Q.INST [`off` |-> `HD c.stack`, `slot` |-> `EL 1 c.stack`,
    `ss` |-> `DROP 2 c.stack`] consolidation_third_address_run, stack_limit_def] >>
  qmatch_goalsub_abbrev_tac `run (s3 with contexts := (c4,rb)::cs)` >>
  mp_tac (Q.INST [`c` |-> `c4`, `s` |-> `s3`, `d` |-> `d3`]
    (Q.INST [`key` |-> `HD c.stack`, `ss` |-> `TL c.stack`]
      system_sload_bounded_run)) >>
  (impl_tac >- (simp[Abbr `c4`, Abbr `s3`, GSYM consolidation_instruction_def,
    consolidation_copy_parse, stack_limit_def] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g4`, `keys4`, `d4`] strip_assume_tac) >>
  qpat_x_assum `run (s3 with contexts := _) = _` (once_rewrite_tac o single) >>
  simp[Abbr `c4`, Abbr `s3`, vfmContextTheory.context_fupdcanon,
    wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w] >> gs[] >>
  simp[Q.INST [`w` |-> `HD c.stack`, `off` |-> `EL 1 c.stack`,
    `ss` |-> `DROP 2 c.stack`,
    `mx` |-> `word_size (w2n (EL 1 c.stack)+32)*32`,
    `cost` |-> `memory_expansion_cost (buffer_length c.memory)
      (word_size (w2n (EL 1 c.stack)+32)*32)`] consolidation_final_store_run,
    stack_limit_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  qmatch_goalsub_abbrev_tac `c with <|stack := _; memory := mf; pc := _; gasUsed := _|>` >>
  `116*(i+1) <= buffer_length mf /\ buffer_length mf <= 1280 /\
    buffer_length mf MOD 32 = 0` by
    (mp_tac (Q.INST [`p` |-> `116*i+84`, `b` |-> `m3`,
      `w` |-> `lookup_storage (slot+3w) storage`] queue_expanded_word_length) >>
     rewrite_tac[GSYM byteTheory.word_to_bytes_be_def,
       cv_stdTheory.word_to_bytes_be_eq_bytes_of_num, listTheory.REVERSE_REVERSE,
       GSYM cv_stdTheory.word_to_bytes_le_eq_bytes_of_num, byteTheory.word_to_bytes_le_def] >>
     simp[LET_THM, Abbr `mf`, Excl "buffer_length_write", Excl "buffer_length_extend"] >>
     strip_tac >> gvs[]) >>
  simp[Q.INST [`idx` |-> `HD c.stack`, `ss` |-> `TL c.stack`]
    consolidation_backedge_run, stack_limit_def] >>
  qmatch_goalsub_abbrev_tac `c with <|stack := _; memory := _; pc := _; gasUsed := gf|>` >>
  qexistsl [`gf`, `keys4`, `d4`, `mf`] >>
  conj_tac >- (simp[Abbr `gf`] >> decide_tac) >>
  conj_tac >- simp[wordsTheory.word_add_n2w] >>
  reverse conj_tac >- simp[] >>
  mp_tac (Q.INST [`b` |-> `c.memory`, `h` |-> `w2n (head:bytes32)`]
    consolidation_expanded_record_memory) >>
  (impl_tac >- simp[]) >> simp_tac pure_ss [LET_THM] >>
  disch_then (mp_tac o cj 8) >>
  simp_tac pure_ss [GSYM wordsTheory.word_add_n2w, GSYM wordsTheory.word_mul_n2w,
    wordsTheory.n2w_w2n] >>
  `4w + (head + n2w i) * 4w = slot` by
    (simp[Abbr `slot`] >> wordsLib.WORD_DECIDE_TAC) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp_tac pure_ss [Abbr `mf`, Abbr `m3`, Abbr `m2`, Abbr `m1`] >>
  rewrite_tac[GSYM byteTheory.word_to_bytes_be_def,
    cv_stdTheory.word_to_bytes_be_eq_bytes_of_num, listTheory.REVERSE_REVERSE,
    GSYM cv_stdTheory.word_to_bytes_le_eq_bytes_of_num, byteTheory.word_to_bytes_le_def] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac std_ss [wordsTheory.WORD_MULT_COMM, wordsTheory.WORD_ADD_ASSOC,
    wordsTheory.WORD_ADD_COMM, arithmeticTheory.ADD_COMM,
    arithmeticTheory.MULT_COMM, arithmeticTheory.LEFT_ADD_DISTRIB] >> simp[]
QED

Theorem consolidation_loop_run[local]:
  c.pc = 233 /\ c.stack = [n2w i; n2w n; head; tail] /\
  c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  297 < LENGTH c.msgParams.code /\ s.msdomain = Collect d /\
  i <= n /\ n <= 2 /\
  116*i <= buffer_length c.memory /\ buffer_length c.memory <= 1280 /\
  buffer_length c.memory MOD 32 = 0 /\
  c.gasUsed + 9523*(n-i)+23 <= c.msgParams.gasLimit ==>
  ?g keys d' m. g <= c.gasUsed + 9523*(n-i)+23 /\
    run (s with contexts := (c,rb)::cs) = run (s with <|
      contexts := (c with <|pc := 297; stack := [n2w n; n2w n; head; tail];
        gasUsed := g; memory := m|>,rb)::cs;
      rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
      msdomain := Collect d'|>) /\
    buffer_take 0 (116*n) m = buffer_take 0 (116*i) c.memory ++
      FLAT (GENLIST (\j. read_consolidation_request
        (lookup_account c.msgParams.callee s.rollback.accounts).storage
        (w2n head+i+j)) (n-i)) /\
    116*n <= buffer_length m /\ buffer_length m <= 1280 /\
    buffer_length m MOD 32 = 0
Proof
  map_every qid_spec_tac [`c`, `s`, `d`] >>
  measureInduct_on `n-i` >> rpt strip_tac >>
  Cases_on `i = n`
  >- (gvs[] >> drule_all consolidation_loop_test_run >>
      disch_then (qspecl_then [`s`, `rb`, `cs`] mp_tac) >> strip_tac >>
      qexistsl [`c.gasUsed+23`, `s.rollback.accesses.storageKeys`, `d`, `c.memory`] >>
      simp[] >>
      qpat_x_assum `s.msdomain = _` (fn th => rewrite_tac[GSYM th]) >>
      simp[vfmContextTheory.context_fupdcanon,
        vfmContextTheory.context_component_equality,
        vfmContextTheory.execution_state_component_equality] >>
      AP_TERM_TAC >> simp[vfmContextTheory.execution_state_component_equality,
        vfmContextTheory.context_component_equality]) >>
  `i < n /\ i < 2 /\ c.gasUsed+23 <= c.msgParams.gasLimit` by decide_tac >>
  `~((n2w i:bytes32) = n2w n)` by
    (simp[wordsTheory.n2w_11, wordsTheory.dimword_def] >> decide_tac) >>
  drule_all consolidation_loop_test_run >>
  disch_then (qspecl_then [`s`, `rb`, `cs`] mp_tac) >> strip_tac >>
  qabbrev_tac `c1 = c with <|pc := 241; stack := [n2w i;n2w n;head;tail];
    gasUsed := c.gasUsed+23|>` >>
  `run (s with contexts := (c,rb)::cs) = run (s with contexts := (c1,rb)::cs)` by
    simp[Abbr `c1`] >>
  mp_tac (Q.INST [`c` |-> `c1`, `cnt` |-> `n2w n`] consolidation_record_run) >>
  (impl_tac >- (simp[Abbr `c1`] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g1`, `keys1`, `d1`, `m1`] strip_assume_tac) >>
  qabbrev_tac `c2 = c1 with <|pc := 233; stack := [n2w (i+1);n2w n;head;tail];
    gasUsed := g1; memory := m1|>` >>
  qabbrev_tac `s2 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys1; msdomain := Collect d1|>` >>
  first_x_assum (qspec_then `i+1` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`d1`, `s2`, `c2`] mp_tac) >>
  (impl_tac >- (simp[Abbr `c2`, Abbr `s2`, Abbr `c1`] >> gvs[] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g2`, `keys2`, `d2`, `m2`] strip_assume_tac) >>
  qexistsl [`g2`, `keys2`, `d2`, `m2`] >>
  conj_tac >- (gvs[Abbr `c2`, Abbr `c1`] >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `run (s with contexts := (c,rb)::cs) = run (s with contexts := (c1,rb)::cs)`
        (once_rewrite_tac o single) >>
      qpat_x_assum `run (s with contexts := (c1,rb)::cs) = _`
        (once_rewrite_tac o single) >>
      qpat_x_assum `run (s2 with contexts := _) = _` (once_rewrite_tac o single) >>
      simp[Abbr `s2`, Abbr `c2`, Abbr `c1`, vfmContextTheory.context_fupdcanon,
        vfmContextTheory.execution_state_fupdcanon]) >>
  reverse conj_tac >- simp[] >>
  gvs[Abbr `c2`, Abbr `c1`, Abbr `s2`] >>
  `n-i = SUC (n-(i+1))` by decide_tac >>
  qpat_x_assum `n-i = _` (once_rewrite_tac o single) >>
  once_rewrite_tac[listTheory.GENLIST_CONS] >>
  simp_tac pure_ss [listTheory.FLAT, combinTheory.o_DEF, arithmeticTheory.ADD_CLAUSES] >>
  BETA_TAC >> simp_tac pure_ss [arithmeticTheory.ADD_CLAUSES] >>
  AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp_tac std_ss [FUN_EQ_THM] >> gen_tac >> AP_TERM_TAC >> decide_tac
QED

Theorem consolidation_copy_run[local]:
  c.pc = 211 /\ c.stack = [] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY consolidation_request_code /\
  297 < LENGTH c.msgParams.code /\ s.msdomain = Collect d /\
  head = lookup_storage 2w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  tail = lookup_storage 3w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  w2n head <= w2n tail /\
  buffer_length c.memory <= 1280 /\ buffer_length c.memory MOD 32 = 0 /\
  c.gasUsed + 4246 + 9523 * MIN 2 (w2n tail-w2n head) + 23 <= c.msgParams.gasLimit ==>
  ?g keys d' m. g <= c.gasUsed + 4246 + 9523 * MIN 2 (w2n tail-w2n head) + 23 /\
    run (s with contexts := (c,rb)::cs) = run (s with <|
      contexts := (c with <|pc := 297;
        stack := [n2w (MIN 2 (w2n tail-w2n head));
                  n2w (MIN 2 (w2n tail-w2n head));head;tail];
        gasUsed := g; memory := m|>,rb)::cs;
      rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
      msdomain := Collect d'|>) /\
    buffer_take 0 (116 * MIN 2 (w2n tail-w2n head)) m =
      FLAT (GENLIST (\j. read_consolidation_request
        (lookup_account c.msgParams.callee s.rollback.accounts).storage (w2n head+j))
        (MIN 2 (w2n tail-w2n head))) /\
    116 * MIN 2 (w2n tail-w2n head) <= buffer_length m /\
    buffer_length m <= 1280 /\ buffer_length m MOD 32 = 0
Proof
  strip_tac >>
  `c.gasUsed + 4246 <= c.msgParams.gasLimit` by decide_tac >>
  `231 < LENGTH c.msgParams.code` by decide_tac >>
  drule_all consolidation_loop_entry_run >>
  disch_then (qspecl_then [`rb`, `cs`]
    (qx_choosel_then [`g1`, `keys1`, `d1`] strip_assume_tac)) >>
  qabbrev_tac `n = MIN 2 (w2n tail-w2n head)` >>
  qabbrev_tac `c1 = c with <|pc := 233; stack := [0w;n2w n;head;tail]; gasUsed := g1|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys1; msdomain := Collect d1|>` >>
  mp_tac (Q.INST [`c` |-> `c1`, `s` |-> `s1`, `i` |-> `0`, `d` |-> `d1`]
    consolidation_loop_run) >>
  (impl_tac >- (simp[Abbr `c1`, Abbr `s1`, Abbr `n`] >> gvs[])) >>
  disch_then (qx_choosel_then [`g2`, `keys2`, `d2`, `m2`] strip_assume_tac) >>
  qexistsl [`g2`, `keys2`, `d2`, `m2`] >>
  conj_tac >- (gvs[Abbr `c1`] >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `run (s with contexts := _) = _` (once_rewrite_tac o single) >>
      qpat_x_assum `run (s1 with contexts := _) = _` (once_rewrite_tac o single) >>
      simp[Abbr `s1`, Abbr `c1`, vfmContextTheory.context_fupdcanon,
        vfmContextTheory.execution_state_fupdcanon]) >>
  gvs[Abbr `s1`, Abbr `c1`] >> simp[vfmBufferTheory.buffer_take_to_list]
QED

Theorem withdrawal_pointer_parse[local]:
  withdrawal_instruction 387 = SOME JumpDest /\
  withdrawal_instruction 388 = SOME (Swap 1) /\
  withdrawal_instruction 389 = SOME Add /\
  withdrawal_instruction 390 = SOME (Dup 0) /\
  withdrawal_instruction 391 = SOME (Swap 2) /\
  withdrawal_instruction 392 = SOME Eq /\
  withdrawal_instruction 393 = SOME (Push 2 [1w;149w]) /\
  withdrawal_instruction 396 = SOME JumpI /\
  withdrawal_instruction 397 = SOME (Swap 0) /\
  withdrawal_instruction 398 = SOME (Push 1 [2w]) /\
  withdrawal_instruction 400 = SOME SStore /\
  withdrawal_instruction 401 = SOME (Push 2 [1w;160w]) /\
  withdrawal_instruction 404 = SOME Jump /\
  withdrawal_instruction 405 = SOME JumpDest /\
  withdrawal_instruction 406 = SOME (Swap 0) /\
  withdrawal_instruction 407 = SOME Pop /\
  withdrawal_instruction 408 = SOME (Push 0 []) /\
  withdrawal_instruction 409 = SOME (Push 1 [2w]) /\
  withdrawal_instruction 411 = SOME SStore /\
  withdrawal_instruction 412 = SOME (Push 0 []) /\
  withdrawal_instruction 413 = SOME (Push 1 [3w]) /\
  withdrawal_instruction 415 = SOME SStore /\
  withdrawal_instruction 416 = SOME JumpDest
Proof
  rpt conj_tac >> CONV_TAC cv_eval
QED

Theorem withdrawal_pointer_test_run[local]:
  c.pc = 387 /\ c.stack = [cnt;cnt;head;tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  405 < LENGTH c.msgParams.code /\ c.gasUsed + 29 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|pc := if head + cnt = tail then 405 else 397;
      stack := [cnt;head+cnt]; gasUsed := c.gasUsed+29|>,rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [149w:byte;1w] = (405w:bytes32)` by
    (simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero,
      byteTheory.word_slice_alt_def] >> wordsLib.WORD_DECIDE_TAC) >>
  simp[SimpLHS, system_jumpdest_run,
    GSYM withdrawal_instruction_def, withdrawal_pointer_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`] system_swap_run,
    GSYM withdrawal_instruction_def, withdrawal_pointer_parse] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`, `f` |-> `(word_add:bytes32->bytes32->bytes32)`]
    system_binop_run, GSYM withdrawal_instruction_def, withdrawal_pointer_parse,
    step_inst_def, is_call_def, static_gas_def, opcode_def, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_pointer_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`] system_swap_run,
    GSYM withdrawal_instruction_def, withdrawal_pointer_parse] >>
  simp[SimpLHS, Q.INST [`op` |-> `Eq`, `f` |-> `(\x y:bytes32. b2w (x=y))`]
    system_binop_run, GSYM withdrawal_instruction_def, withdrawal_pointer_parse,
    step_inst_def, is_call_def, static_gas_def, opcode_def, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`, `ws` |-> `[1w:byte;149w]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_pointer_parse,
    static_gas_def, opcode_def, stack_limit_def] >>
  Cases_on `head+cnt = tail` >>
  simp[SimpLHS, system_jumpi_run, b2w_def, wordsTheory.dimword_def,
    GSYM withdrawal_instruction_def, withdrawal_pointer_parse] >>
  simp[vfmContextTheory.context_fupdcanon, wordsTheory.WORD_ADD_COMM] >> gvs[]
QED

Theorem withdrawal_pointer_jump_run[local]:
  c.pc = 401 /\ c.stack = [cnt] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  416 < LENGTH c.msgParams.code /\ c.gasUsed + 11 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|pc := 416; stack := [cnt]; gasUsed := c.gasUsed+11|>,rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [160w:byte;1w] = (416w:bytes32)` by
    (simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero,
      byteTheory.word_slice_alt_def] >> wordsLib.WORD_DECIDE_TAC) >>
  simp[SimpLHS, Q.INST [`n` |-> `2`, `ws` |-> `[1w:byte;160w]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_pointer_parse,
    static_gas_def, opcode_def, stack_limit_def] >>
  simp[SimpLHS, system_jump_run, wordsTheory.dimword_def,
    GSYM withdrawal_instruction_def, withdrawal_pointer_parse] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_pointer_advance_run[local]:
  c.pc = 397 /\ c.stack = [cnt;newhead] /\ c.jumpDest = NONE /\
  ~c.msgParams.static /\ s.msdomain = Collect d /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  416 < LENGTH c.msgParams.code /\ c.gasUsed + 22117 <= c.msgParams.gasLimit ==>
  ?g ad su keys d'. g <= c.gasUsed+22117 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := 416; stack := [cnt]; gasUsed := g;
      addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>,rb)::cs;
    rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          update_storage 2w newhead) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `word_of_bytes F 0w [2w:byte] = (2w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  qabbrev_tac `c1 = c with <|pc := 400; stack := [2w;newhead;cnt];
    gasUsed := c.gasUsed+6|>` >>
  `run (s with contexts := (c,rb)::cs) = run (s with contexts := (c1,rb)::cs)` by
    (simp[SimpLHS, Q.INST [`n` |-> `0`] system_swap_run,
      GSYM withdrawal_instruction_def, withdrawal_pointer_parse] >>
     simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[2w:byte]`] system_push_run,
      GSYM withdrawal_instruction_def, withdrawal_pointer_parse,
      static_gas_def, opcode_def, stack_limit_def] >>
     simp[Abbr `c1`, vfmContextTheory.context_fupdcanon]) >>
  mp_tac (Q.INST [`c` |-> `c1`, `key` |-> `2w:bytes32`,
    `value` |-> `newhead`, `ss` |-> `[cnt]`] system_sstore_bounded_run) >>
  (impl_tac >- (simp[Abbr `c1`, GSYM withdrawal_instruction_def,
    withdrawal_pointer_parse] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g1`, `ad`, `su`, `keys`, `d1`] strip_assume_tac) >>
  qexistsl [`g1+11`, `ad`, `su`, `keys`, `d1`] >>
  conj_tac >- (gvs[Abbr `c1`] >> decide_tac) >>
  qpat_x_assum `run (s with contexts := (c,rb)::cs) = _` (once_rewrite_tac o single) >>
  qpat_x_assum `run (s with contexts := (c1,rb)::cs) = _` (once_rewrite_tac o single) >>
  `g1+11 <= c.msgParams.gasLimit` by (gvs[Abbr `c1`] >> decide_tac) >>
  mp_tac (Q.INST [`c` |-> `c with <|pc := 401; stack := [cnt]; gasUsed := g1;
    addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>`,
    `s` |-> `s with <|rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          update_storage 2w newhead) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
      msdomain := Collect d1|>`] withdrawal_pointer_jump_run) >>
  simp[Abbr `c1`, vfmContextTheory.context_fupdcanon,
    vfmContextTheory.execution_state_fupdcanon]
QED

Theorem withdrawal_pointer_reset_prefix_run[local]:
  c.pc = 405 /\ c.stack = [cnt;tail] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  c.gasUsed+6 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|pc := 408; stack := [cnt]; gasUsed := c.gasUsed+6|>,rb)::cs)
Proof
  strip_tac >>
  simp[SimpLHS, system_jumpdest_run,
    GSYM withdrawal_instruction_def, withdrawal_pointer_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_swap_run,
    GSYM withdrawal_instruction_def, withdrawal_pointer_parse] >>
  simp[SimpLHS, system_pop_run,
    GSYM withdrawal_instruction_def, withdrawal_pointer_parse] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_pointer_reset_run[local]:
  c.pc = 405 /\ c.stack = [cnt;tail] /\ c.jumpDest = NONE /\
  ~c.msgParams.static /\ s.msdomain = Collect d /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  c.gasUsed+44216 <= c.msgParams.gasLimit ==>
  ?g ad su keys d'. g <= c.gasUsed+44216 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := 416; stack := [cnt]; gasUsed := g;
      addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>,rb)::cs;
    rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          (update_storage 3w 0w o update_storage 2w 0w)) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `c.gasUsed+6 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all withdrawal_pointer_reset_prefix_run >>
  disch_then (qspecl_then [`s`, `rb`, `cs`] mp_tac) >> strip_tac >>
  qabbrev_tac `c1 = c with <|pc := 408; stack := [cnt]; gasUsed := c.gasUsed+6|>` >>
  mp_tac (Q.INST [`c` |-> `c1`, `slot` |-> `2w:byte`] system_clear_slot_run) >>
  (impl_tac >- simp[Abbr `c1`, GSYM withdrawal_instruction_def,
    withdrawal_pointer_parse, stack_limit_def]) >>
  disch_then (qx_choosel_then [`g1`, `ad1`, `su1`, `keys1`, `d1`] strip_assume_tac) >>
  qabbrev_tac `c2 = c1 with <|pc := 412; gasUsed := g1;
    addRefund := ad1+c.addRefund; subRefund := su1+c.subRefund|>` >>
  qabbrev_tac `s2 = s with <|rollback := s.rollback with <|
    accounts := update_account c.msgParams.callee
      ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
        update_storage 2w 0w) s.rollback.accounts;
    accesses := s.rollback.accesses with storageKeys := keys1|>;
    msdomain := Collect d1|>` >>
  mp_tac (Q.INST [`c` |-> `c2`, `s` |-> `s2`, `d` |-> `d1`,
    `slot` |-> `3w:byte`] system_clear_slot_run) >>
  (impl_tac >- (simp[Abbr `c2`, Abbr `c1`, Abbr `s2`, GSYM withdrawal_instruction_def,
    withdrawal_pointer_parse, stack_limit_def] >> gvs[] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g2`, `ad2`, `su2`, `keys2`, `d2`] strip_assume_tac) >>
  qexistsl [`g2`, `ad2+ad1`, `su2+su1`, `keys2`, `d2`] >>
  conj_tac >- (gvs[Abbr `c2`, Abbr `c1`] >> decide_tac) >>
  qpat_x_assum `run (s with contexts := (c,rb)::cs) = _` (once_rewrite_tac o single) >>
  qpat_x_assum `run (s with contexts := (c1,rb)::cs) = _` (once_rewrite_tac o single) >>
  qpat_x_assum `run (s2 with contexts := _) = _` mp_tac >>
  simp_tac pure_ss [Abbr `s2`, Abbr `c2`, Abbr `c1`] >>
  simp_tac (srw_ss()) [vfmContextTheory.context_fupdcanon,
    vfmContextTheory.execution_state_fupdcanon,
    vfmContextTheory.rollback_state_fupdcanon, vfmContextTheory.access_sets_fupdcanon,
    arithmeticTheory.ADD_ASSOC] >>
  simp_tac (srw_ss()) [vfmStateTheory.lookup_account_def,
    vfmStateTheory.update_account_def, combinTheory.UPDATE_APPLY,
    combinTheory.UPDATE_EQ, vfmStateTheory.account_state_fupdcanon,
    combinTheory.o_DEF]
QED

Theorem withdrawal_pointer_run[local]:
  c.pc = 387 /\ c.stack = [cnt;cnt;head;tail] /\ c.jumpDest = NONE /\
  ~c.msgParams.static /\ s.msdomain = Collect d /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  416 < LENGTH c.msgParams.code /\ c.gasUsed+44245 <= c.msgParams.gasLimit ==>
  ?g ad su keys d'. g <= c.gasUsed+44245 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := 416; stack := [cnt]; gasUsed := g;
      addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>,rb)::cs;
    rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          (if head+cnt = tail then update_storage 3w 0w o update_storage 2w 0w
           else update_storage 2w (head+cnt))) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `405 < LENGTH c.msgParams.code /\ c.gasUsed+29 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all withdrawal_pointer_test_run >>
  disch_then (qspecl_then [`s`, `rb`, `cs`] mp_tac) >> strip_tac >>
  qabbrev_tac `c1 = c with <|pc := if head+cnt = tail then 405 else 397;
    stack := [cnt;head+cnt]; gasUsed := c.gasUsed+29|>` >>
  Cases_on `head+cnt = tail`
  >- (mp_tac (Q.INST [`c` |-> `c1`, `tail` |-> `tail`]
        withdrawal_pointer_reset_run) >>
      (impl_tac >- simp[Abbr `c1`]) >>
      disch_then (qx_choosel_then [`g`, `ad`, `su`, `keys`, `d1`] strip_assume_tac) >>
      qexistsl [`g`, `ad`, `su`, `keys`, `d1`] >>
      conj_tac >- (gvs[Abbr `c1`] >> decide_tac) >>
      gvs[Abbr `c1`, vfmContextTheory.context_fupdcanon]) >>
  mp_tac (Q.INST [`c` |-> `c1`, `newhead` |-> `head+cnt`]
    withdrawal_pointer_advance_run) >>
  (impl_tac >- simp[Abbr `c1`]) >>
  disch_then (qx_choosel_then [`g`, `ad`, `su`, `keys`, `d1`] strip_assume_tac) >>
  qexistsl [`g`, `ad`, `su`, `keys`, `d1`] >>
  conj_tac >- (gvs[Abbr `c1`] >> decide_tac) >>
  gvs[Abbr `c1`, vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_excess_parse[local]:
  withdrawal_instruction 416 = SOME JumpDest /\
  withdrawal_instruction 417 = SOME (Push 0 []) /\
  withdrawal_instruction 418 = SOME SLoad /\
  withdrawal_instruction 419 = SOME (Dup 0) /\
  withdrawal_instruction 420 = SOME (Push 32 (REPLICATE 32 255w)) /\
  withdrawal_instruction 453 = SOME Eq /\
  withdrawal_instruction 454 = SOME IsZero /\
  withdrawal_instruction 455 = SOME (Push 2 [1w;205w]) /\
  withdrawal_instruction 458 = SOME JumpI /\
  withdrawal_instruction 459 = SOME Pop /\
  withdrawal_instruction 460 = SOME (Push 0 []) /\
  withdrawal_instruction 461 = SOME JumpDest /\
  withdrawal_instruction 462 = SOME (Push 1 [1w]) /\
  withdrawal_instruction 464 = SOME SLoad /\
  withdrawal_instruction 465 = SOME (Push 1 [2w]) /\
  withdrawal_instruction 467 = SOME (Dup 2) /\
  withdrawal_instruction 468 = SOME (Dup 2) /\
  withdrawal_instruction 469 = SOME Add /\
  withdrawal_instruction 470 = SOME GT /\
  withdrawal_instruction 471 = SOME (Push 2 [1w;226w]) /\
  withdrawal_instruction 474 = SOME JumpI /\
  withdrawal_instruction 475 = SOME Pop /\
  withdrawal_instruction 476 = SOME Pop /\
  withdrawal_instruction 477 = SOME (Push 0 []) /\
  withdrawal_instruction 478 = SOME (Push 2 [1w;232w]) /\
  withdrawal_instruction 481 = SOME Jump /\
  withdrawal_instruction 482 = SOME JumpDest /\
  withdrawal_instruction 483 = SOME Add /\
  withdrawal_instruction 484 = SOME (Push 1 [2w]) /\
  withdrawal_instruction 486 = SOME (Swap 0) /\
  withdrawal_instruction 487 = SOME Sub /\
  withdrawal_instruction 488 = SOME JumpDest /\
  withdrawal_instruction 489 = SOME (Push 0 []) /\
  withdrawal_instruction 490 = SOME SStore /\
  withdrawal_instruction 491 = SOME (Push 0 []) /\
  withdrawal_instruction 492 = SOME (Push 1 [1w]) /\
  withdrawal_instruction 494 = SOME SStore /\
  withdrawal_instruction 495 = SOME (Push 1 [76w]) /\
  withdrawal_instruction 497 = SOME Mul /\
  withdrawal_instruction 498 = SOME (Push 0 []) /\
  withdrawal_instruction 499 = SOME Return
Proof
  rpt conj_tac >> CONV_TAC cv_eval
QED

Theorem withdrawal_push_inhibitor[local]:
  word_of_bytes F 0w (REVERSE (REPLICATE 32 (255w:byte))) = (-1w:bytes32)
Proof
  dep_rewrite.DEP_ONCE_REWRITE_TAC[byteTheory.word_of_bytes_eq_or] >>
  conj_tac >- EVAL_TAC >>
  EVAL_TAC
QED

Theorem withdrawal_inhibitor_run[local]:
  c.pc = 419 /\ c.stack = [excess;cnt] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  461 < LENGTH c.msgParams.code /\
  c.gasUsed+29 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|pc := 461; stack := [if excess = -1w then 0w else excess;cnt];
      gasUsed := c.gasUsed+(if excess = -1w then 29 else 25)|>,rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [205w:byte;1w] = (461w:bytes32)` by
    (dep_rewrite.DEP_ONCE_REWRITE_TAC[byteTheory.word_of_bytes_eq_or] >>
     conj_tac >- EVAL_TAC >> EVAL_TAC) >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `32`, `ws` |-> `REPLICATE 32 (255w:byte)`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    static_gas_def, opcode_def, withdrawal_push_inhibitor] >>
  simp[SimpLHS, Q.INST [`op` |-> `Eq`, `f` |-> `(\x y:bytes32. b2w (x = y))`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `IsZero`, `f` |-> `(\x:bytes32. b2w (x = 0w))`] system_monop_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`, `ws` |-> `[1w:byte;205w]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  Cases_on `excess = -1w` >>
  simp[SimpLHS, system_jumpi_run, b2w_def, wordsTheory.dimword_def,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse] >>
  simp[] >>
  simp[SimpLHS, system_pop_run,
    Q.INST [`n` |-> `0`, `ws` |-> `[]:byte list`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    static_gas_def, opcode_def, byteTheory.word_of_bytes_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_excess_load_run[local]:
  c.pc = 416 /\ c.stack = [cnt] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  461 < LENGTH c.msgParams.code /\ s.msdomain = Collect d /\
  c.gasUsed+2132 <= c.msgParams.gasLimit ==>
  ?g keys d'. g <= c.gasUsed+2132 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := 461; gasUsed := g;
      stack := [if lookup_storage 0w (lookup_account c.msgParams.callee s.rollback.accounts).storage = -1w
                then 0w else lookup_storage 0w (lookup_account c.msgParams.callee s.rollback.accounts).storage;cnt]|>,rb)::cs;
    rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  qabbrev_tac `c1 = c with <|pc := 418; stack := [0w;cnt]; gasUsed := c.gasUsed+3|>` >>
  `run (s with contexts := (c,rb)::cs) = run (s with contexts := (c1,rb)::cs)` by
    (simp[SimpLHS, system_jumpdest_run, GSYM withdrawal_instruction_def,
       withdrawal_excess_parse] >> simp[] >>
     simp[SimpLHS, Q.INST [`n` |-> `0`, `ws` |-> `[]:byte list`] system_push_run,
       GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
       static_gas_def, opcode_def, byteTheory.word_of_bytes_def] >>
     simp[Abbr `c1`, vfmContextTheory.context_fupdcanon]) >>
  mp_tac (Q.INST [`c` |-> `c1`, `key` |-> `0w:bytes32`, `ss` |-> `[cnt:bytes32]`]
    system_sload_bounded_run) >>
  (impl_tac >- simp[Abbr `c1`, GSYM withdrawal_instruction_def,
    withdrawal_excess_parse, stack_limit_def]) >>
  disch_then (qx_choosel_then [`g1`, `keys`, `d1`] strip_assume_tac) >>
  qabbrev_tac `excess = lookup_storage 0w (lookup_account c.msgParams.callee s.rollback.accounts).storage` >>
  qabbrev_tac `c2 = c with <|pc := 419; stack := [excess;cnt]; gasUsed := g1|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys; msdomain := Collect d1|>` >>
  mp_tac (Q.INST [`c` |-> `c2`, `s` |-> `s1`] withdrawal_inhibitor_run) >>
  (impl_tac >- (simp[Abbr `c2`] >> gvs[Abbr `c1`])) >>
  strip_tac >>
  qexistsl [`g1+(if excess = -1w then 29 else 25)`, `keys`, `d1`] >>
  conj_tac >- (gvs[Abbr `c1`] >> IF_CASES_TAC >> decide_tac) >>
  gvs[Abbr `c1`, Abbr `c2`, Abbr `s1`, Abbr `excess`, vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_excess_test_run[local]:
  c.pc = 465 /\ c.stack = [added;excess;cnt] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  482 < LENGTH c.msgParams.code /\ c.gasUsed+28 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|pc := if 2 < w2n (added+excess) then 482 else 475;
      stack := [added;excess;cnt]; gasUsed := c.gasUsed+28|>,rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [2w:byte] = (2w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  `word_of_bytes F 0w [226w:byte;1w] = (482w:bytes32)` by
    (dep_rewrite.DEP_ONCE_REWRITE_TAC[byteTheory.word_of_bytes_eq_or] >>
     conj_tac >- EVAL_TAC >> EVAL_TAC) >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[2w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`] system_dup_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`, `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `GT`, `f` |-> `(\x y:bytes32. b2w (w2n x > w2n y))`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`, `ws` |-> `[1w:byte;226w]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  Cases_on `2 < w2n (added+excess)` >>
  simp[SimpLHS, system_jumpi_run, b2w_def, wordsTheory.dimword_def,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, arithmeticTheory.GREATER_DEF] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_excess_zero_run[local]:
  c.pc = 475 /\ c.stack = [added;excess;cnt] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  488 < LENGTH c.msgParams.code /\ c.gasUsed+17 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|pc := 488; stack := [0w;cnt]; gasUsed := c.gasUsed+17|>,rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [232w:byte;1w] = (488w:bytes32)` by
    (dep_rewrite.DEP_ONCE_REWRITE_TAC[byteTheory.word_of_bytes_eq_or] >>
     conj_tac >- EVAL_TAC >> EVAL_TAC) >>
  simp[SimpLHS, system_pop_run, GSYM withdrawal_instruction_def, withdrawal_excess_parse] >>
  simp[SimpLHS, system_pop_run, GSYM withdrawal_instruction_def, withdrawal_excess_parse] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`, `ws` |-> `[]:byte list`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    static_gas_def, opcode_def, byteTheory.word_of_bytes_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `2`, `ws` |-> `[1w:byte;232w]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, system_jump_run, GSYM withdrawal_instruction_def, withdrawal_excess_parse,
    wordsTheory.dimword_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_excess_sub_run[local]:
  c.pc = 482 /\ c.stack = [added;excess;cnt] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  c.gasUsed+13 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|pc := 488; stack := [added+excess-2w;cnt]; gasUsed := c.gasUsed+13|>,rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [2w:byte] = (2w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, system_jumpdest_run, GSYM withdrawal_instruction_def, withdrawal_excess_parse] >>
  simp[] >>
  simp[SimpLHS, Q.INST [`op` |-> `Add`, `f` |-> `word_add:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[2w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`] system_swap_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Sub`, `f` |-> `word_sub:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[vfmContextTheory.context_fupdcanon, wordsTheory.WORD_SUB_ADD]
QED

Theorem withdrawal_excess_arithmetic_run[local]:
  c.pc = 465 /\ c.stack = [added;excess;cnt] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  488 < LENGTH c.msgParams.code /\ c.gasUsed+45 <= c.msgParams.gasLimit ==>
  ?g. g <= c.gasUsed+45 /\
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|pc := 488;
      stack := [if 2 < w2n (added+excess) then added+excess-2w else 0w;cnt];
      gasUsed := g|>,rb)::cs)
Proof
  strip_tac >>
  `482 < LENGTH c.msgParams.code /\ c.gasUsed+28 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all withdrawal_excess_test_run >>
  disch_then (qspecl_then [`s`, `rb`, `cs`] mp_tac) >> strip_tac >>
  qabbrev_tac `c1 = c with <|pc := if 2 < w2n (added+excess) then 482 else 475;
    stack := [added;excess;cnt]; gasUsed := c.gasUsed+28|>` >>
  Cases_on `2 < w2n (added+excess)`
  >- (qexists_tac `c.gasUsed+41` >> conj_tac >- decide_tac >>
      mp_tac (Q.INST [`c` |-> `c1`] withdrawal_excess_sub_run) >>
      (impl_tac >- simp[Abbr `c1`]) >>
      gvs[Abbr `c1`, vfmContextTheory.context_fupdcanon]) >>
  qexists_tac `c.gasUsed+45` >> conj_tac >- decide_tac >>
  mp_tac (Q.INST [`c` |-> `c1`] withdrawal_excess_zero_run) >>
  (impl_tac >- simp[Abbr `c1`]) >>
  gvs[Abbr `c1`, vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_added_load_run[local]:
  c.pc = 461 /\ c.stack = [excess;cnt] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  s.msdomain = Collect d /\ c.gasUsed+2104 <= c.msgParams.gasLimit ==>
  ?g keys d'. g <= c.gasUsed+2104 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := 465; gasUsed := g;
      stack := [lookup_storage 1w (lookup_account c.msgParams.callee s.rollback.accounts).storage;excess;cnt]|>,rb)::cs;
    rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  qabbrev_tac `c1 = c with <|pc := 462; gasUsed := c.gasUsed+1|>` >>
  `run (s with contexts := (c,rb)::cs) = run (s with contexts := (c1,rb)::cs)` by
    (simp[SimpLHS, system_jumpdest_run, GSYM withdrawal_instruction_def,
       withdrawal_excess_parse] >>
     simp[Abbr `c1`, vfmContextTheory.context_fupdcanon]) >>
  mp_tac (Q.INST [`c` |-> `c1`, `slot` |-> `1w:byte`] system_push1_sload_run) >>
  (impl_tac >- simp[Abbr `c1`, GSYM withdrawal_instruction_def,
    withdrawal_excess_parse, stack_limit_def]) >>
  disch_then (qx_choosel_then [`g`, `keys`, `d'`] strip_assume_tac) >>
  qexistsl [`g`, `keys`, `d'`] >>
  conj_tac >- gvs[Abbr `c1`] >>
  gvs[Abbr `c1`, vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_excess_store_run[local]:
  c.pc = 488 /\ c.stack = [value;cnt] /\ c.jumpDest = NONE /\
  ~c.msgParams.static /\ s.msdomain = Collect d /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  c.gasUsed+22103 <= c.msgParams.gasLimit ==>
  ?g ad su keys d'. g <= c.gasUsed+22103 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := 491; stack := [cnt]; gasUsed := g;
      addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>,rb)::cs;
    rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          update_storage 0w value) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  qabbrev_tac `c1 = c with <|pc := 490; stack := [0w;value;cnt]; gasUsed := c.gasUsed+3|>` >>
  `run (s with contexts := (c,rb)::cs) = run (s with contexts := (c1,rb)::cs)` by
    (simp[SimpLHS, system_jumpdest_run, GSYM withdrawal_instruction_def,
       withdrawal_excess_parse] >> simp[] >>
     simp[SimpLHS, Q.INST [`n` |-> `0`, `ws` |-> `[]:byte list`] system_push_run,
       GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
       static_gas_def, opcode_def, byteTheory.word_of_bytes_def] >>
     simp[Abbr `c1`, vfmContextTheory.context_fupdcanon]) >>
  mp_tac (Q.INST [`c` |-> `c1`, `key` |-> `0w:bytes32`, `ss` |-> `[cnt:bytes32]`]
    system_sstore_bounded_run) >>
  (impl_tac >- simp[Abbr `c1`, GSYM withdrawal_instruction_def,
    withdrawal_excess_parse, stack_limit_def]) >>
  disch_then (qx_choosel_then [`g`, `ad`, `su`, `keys`, `d'`] strip_assume_tac) >>
  qexistsl [`g`, `ad`, `su`, `keys`, `d'`] >>
  conj_tac >- gvs[Abbr `c1`] >>
  gvs[Abbr `c1`, vfmContextTheory.context_fupdcanon]
QED

Theorem queue_excess_word:
  w2n (a:bytes32)+w2n b < dimword (:256) /\ target < dimword (:256) ==>
  (if target < w2n (a+b) then a+b-n2w target else 0w) =
    n2w (w2n a+w2n b-target)
Proof
  strip_tac >>
  `w2n (a+b) = w2n a+w2n b` by simp[wordsTheory.w2n_add_2] >>
  Cases_on `target < w2n (a+b)` >> simp[]
  >- (simp[wordsTheory.n2w_sub, wordsTheory.n2w_w2n,
        GSYM wordsTheory.word_add_n2w]) >>
  simp[wordsTheory.n2w_sub_eq_0]
QED

Theorem withdrawal_excess_compute_run[local]:
  c.pc = 416 /\ c.stack = [cnt] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  488 < LENGTH c.msgParams.code /\ s.msdomain = Collect d /\
  excess = (if lookup_storage 0w (lookup_account c.msgParams.callee s.rollback.accounts).storage = -1w
    then 0w else lookup_storage 0w (lookup_account c.msgParams.callee s.rollback.accounts).storage) /\
  added = lookup_storage 1w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  c.gasUsed+4281 <= c.msgParams.gasLimit ==>
  ?g keys d'. g <= c.gasUsed+4281 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := 488; gasUsed := g;
      stack := [if 2 < w2n (added+excess) then added+excess-2w else 0w;cnt]|>,rb)::cs;
    rollback := s.rollback with accesses := s.rollback.accesses with storageKeys := keys;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `461 < LENGTH c.msgParams.code /\ c.gasUsed+2132 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all withdrawal_excess_load_run >>
  disch_then (qspecl_then [`rb`, `cs`] mp_tac) >>
  disch_then (qx_choosel_then [`g1`, `keys1`, `d1`] strip_assume_tac) >>
  qabbrev_tac `c1 = c with <|pc := 461; stack := [excess;cnt]; gasUsed := g1|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys1; msdomain := Collect d1|>` >>
  mp_tac (Q.INST [`c` |-> `c1`, `s` |-> `s1`, `d` |-> `d1`] withdrawal_added_load_run) >>
  (impl_tac >- (simp[Abbr `c1`, Abbr `s1`] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g2`, `keys2`, `d2`] strip_assume_tac) >>
  qabbrev_tac `c2 = c with <|pc := 465; stack := [added;excess;cnt]; gasUsed := g2|>` >>
  qabbrev_tac `s2 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys2; msdomain := Collect d2|>` >>
  mp_tac (Q.INST [`c` |-> `c2`, `s` |-> `s2`] withdrawal_excess_arithmetic_run) >>
  (impl_tac >- (simp[Abbr `c2`] >> gvs[Abbr `c1`] >> decide_tac)) >>
  disch_then (qx_choose_then `g3` strip_assume_tac) >>
  qexistsl [`g3`, `keys2`, `d2`] >>
  conj_tac >- (gvs[Abbr `c1`, Abbr `c2`] >> decide_tac) >>
  gvs[Abbr `c1`, Abbr `c2`, Abbr `s1`, Abbr `s2`, vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_counter_clear_run[local]:
  c.pc = 491 /\ c.stack = [cnt] /\ c.jumpDest = NONE /\
  ~c.msgParams.static /\ s.msdomain = Collect d /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  c.gasUsed+22105 <= c.msgParams.gasLimit ==>
  ?g ad su keys d'. g <= c.gasUsed+22105 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := 495; gasUsed := g;
      addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>,rb)::cs;
    rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          update_storage 1w 0w) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  mp_tac (Q.INST [`slot` |-> `1w:byte`] system_clear_slot_run) >>
  (impl_tac >- simp[GSYM withdrawal_instruction_def, withdrawal_excess_parse,
    stack_limit_def]) >> simp[]
QED

Theorem withdrawal_excess_bookkeeping_run[local]:
  c.pc = 416 /\ c.stack = [cnt] /\ c.jumpDest = NONE /\
  ~c.msgParams.static /\ s.msdomain = Collect d /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  488 < LENGTH c.msgParams.code /\
  excess = (if lookup_storage 0w (lookup_account c.msgParams.callee s.rollback.accounts).storage = -1w
    then 0w else lookup_storage 0w (lookup_account c.msgParams.callee s.rollback.accounts).storage) /\
  added = lookup_storage 1w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  value = (if 2 < w2n (added+excess) then added+excess-2w else 0w) /\
  c.gasUsed+48489 <= c.msgParams.gasLimit ==>
  ?g ad su keys d'. g <= c.gasUsed+48489 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := 495; gasUsed := g;
      addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>,rb)::cs;
    rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          (update_storage 1w 0w o update_storage 0w value)) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `c.gasUsed+4281 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all withdrawal_excess_compute_run >>
  disch_then (qspecl_then [`rb`, `cs`] mp_tac) >>
  disch_then (qx_choosel_then [`g1`, `keys1`, `d1`] strip_assume_tac) >>
  qabbrev_tac `c1 = c with <|pc := 488; stack := [value;cnt]; gasUsed := g1|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with accesses :=
    s.rollback.accesses with storageKeys := keys1; msdomain := Collect d1|>` >>
  mp_tac (Q.INST [`c` |-> `c1`, `s` |-> `s1`, `d` |-> `d1`] withdrawal_excess_store_run) >>
  (impl_tac >- (simp[Abbr `c1`, Abbr `s1`] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g2`, `ad2`, `su2`, `keys2`, `d2`] strip_assume_tac) >>
  qabbrev_tac `c2 = c with <|pc := 491; stack := [cnt]; gasUsed := g2;
    addRefund := ad2+c.addRefund; subRefund := su2+c.subRefund|>` >>
  qabbrev_tac `s2 = s with <|rollback := s.rollback with <|
    accounts := update_account c.msgParams.callee
      ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
        update_storage 0w value) s.rollback.accounts;
    accesses := s.rollback.accesses with storageKeys := keys2|>; msdomain := Collect d2|>` >>
  mp_tac (Q.INST [`c` |-> `c2`, `s` |-> `s2`, `d` |-> `d2`] withdrawal_counter_clear_run) >>
  (impl_tac >- (simp[Abbr `c2`, Abbr `s2`] >> gvs[Abbr `c1`] >> decide_tac)) >>
  disch_then (qx_choosel_then [`g3`, `ad3`, `su3`, `keys3`, `d3`] strip_assume_tac) >>
  qexistsl [`g3`, `ad3+ad2`, `su3+su2`, `keys3`, `d3`] >>
  conj_tac >- (gvs[Abbr `c1`, Abbr `c2`] >> decide_tac) >>
  qpat_x_assum `run (s with contexts := (c,rb)::cs) = _` mp_tac >>
  qpat_x_assum `run (s1 with contexts := _) = _` mp_tac >>
  qpat_x_assum `run (s2 with contexts := _) = _` mp_tac >>
  qpat_assum `value = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  simp_tac pure_ss [Abbr `s2`, Abbr `c2`, Abbr `s1`, Abbr `c1`] >>
  simp_tac (srw_ss()) [vfmContextTheory.context_fupdcanon,
    vfmContextTheory.execution_state_fupdcanon,
    vfmContextTheory.rollback_state_fupdcanon, vfmContextTheory.access_sets_fupdcanon,
    arithmeticTheory.ADD_ASSOC] >>
  simp_tac (srw_ss()) [vfmStateTheory.lookup_account_def,
    vfmStateTheory.update_account_def, combinTheory.UPDATE_APPLY,
    combinTheory.UPDATE_EQ, vfmStateTheory.account_state_fupdcanon, combinTheory.o_DEF] >>
  Cases_on `c` >> gvs[vfmContextTheory.context_fn_updates]
QED

Theorem queue_return_allocated_run:
  c.stack = [0w;sz] /\ c.msgParams.outputTo = empty_return_destination /\
  FLOOKUP c.msgParams.parsed c.pc = SOME Return /\
  buffer_length c.memory MOD 32 = 0 /\ w2n sz <= buffer_length c.memory /\
  c.gasUsed <= c.msgParams.gasLimit ==>
  run (s with contexts := [(c,rb)]) = SOME (INR NONE,
    s with contexts := [(c with <|stack := [];
      returnData := buffer_take 0 (w2n sz) c.memory|>,rb)])
Proof
  strip_tac >>
  `memory_expansion_cost (buffer_length c.memory) (word_size (w2n sz)*32) = 0 /\
   buffer_extend (MAX (buffer_length c.memory) (word_size (w2n sz)*32)-buffer_length c.memory)
     c.memory = c.memory` by metis_tac[queue_allocated_expansion] >>
  mp_tac (Q.INST [`offset` |-> `0w:bytes32`, `mx` |-> `word_size (w2n sz)*32`,
    `cost` |-> `0`, `mem` |-> `c.memory`] system_return_run) >>
  (impl_tac >- (simp[] >> Cases_on `w2n sz = 0` >>
    simp[word_size_def])) >>
  simp[] >> Cases_on `c` >> simp[vfmContextTheory.context_fn_updates]
QED

Theorem withdrawal_bookkeeping_run[local]:
  c.pc = 387 /\ c.stack = [cnt;cnt;head;tail] /\ c.jumpDest = NONE /\
  ~c.msgParams.static /\ s.msdomain = Collect d /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  488 < LENGTH c.msgParams.code /\
  excess = (if lookup_storage 0w (lookup_account c.msgParams.callee s.rollback.accounts).storage = -1w
    then 0w else lookup_storage 0w (lookup_account c.msgParams.callee s.rollback.accounts).storage) /\
  added = lookup_storage 1w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  w2n added+w2n excess < dimword (:256) /\
  c.gasUsed+92734 <= c.msgParams.gasLimit ==>
  ?g ad su keys d'. g <= c.gasUsed+92734 /\
  run (s with contexts := (c,rb)::cs) = run (s with <|
    contexts := (c with <|pc := 495; stack := [cnt]; gasUsed := g;
      addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>,rb)::cs;
    rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          ((if head+cnt = tail then update_storage 3w 0w o update_storage 2w 0w
            else update_storage 2w (head+cnt)) o update_storage 1w 0w o
           update_storage 0w (n2w (w2n added+w2n excess-2)))) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `416 < LENGTH c.msgParams.code /\ c.gasUsed+44245 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all withdrawal_pointer_run >>
  disch_then (qspecl_then [`rb`, `cs`] mp_tac) >>
  disch_then (qx_choosel_then [`g1`, `ad1`, `su1`, `keys1`, `d1`] strip_assume_tac) >>
  qabbrev_tac `c1 = c with <|pc := 416; stack := [cnt]; gasUsed := g1;
    addRefund := ad1+c.addRefund; subRefund := su1+c.subRefund|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with <|
    accounts := update_account c.msgParams.callee
      ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
        (if head+cnt = tail then update_storage 3w 0w o update_storage 2w 0w
         else update_storage 2w (head+cnt))) s.rollback.accounts;
    accesses := s.rollback.accesses with storageKeys := keys1|>; msdomain := Collect d1|>` >>
  mp_tac (Q.INST [`c` |-> `c1`, `s` |-> `s1`, `d` |-> `d1`,
    `value` |-> `n2w (w2n added+w2n excess-2):bytes32`] withdrawal_excess_bookkeeping_run) >>
  (impl_tac >- (simp[Abbr `c1`, Abbr `s1`] >>
    conj_tac >- (Cases_on `head+cnt = tail` >>
      gvs[vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
        vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
        combinTheory.UPDATE_APPLY, combinTheory.o_DEF, wordsTheory.dimword_def]) >>
    conj_tac >- (Cases_on `head+cnt = tail` >>
      gvs[vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
        vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
        combinTheory.UPDATE_APPLY, combinTheory.o_DEF, wordsTheory.dimword_def]) >>
    mp_tac (Q.INST [`a` |-> `added:bytes32`, `b` |-> `excess:bytes32`,
      `target` |-> `2`] queue_excess_word) >>
    (impl_tac >- simp[wordsTheory.dimword_def]) >> simp[])) >>
  disch_then (qx_choosel_then [`g2`, `ad2`, `su2`, `keys2`, `d2`] strip_assume_tac) >>
  qexistsl [`g2`, `ad2+ad1`, `su2+su1`, `keys2`, `d2`] >>
  conj_tac >- (gvs[Abbr `c1`] >> decide_tac) >>
  qpat_x_assum `run (s with contexts := (c,rb)::cs) = _` mp_tac >>
  qpat_x_assum `run (s1 with contexts := _) = _` mp_tac >>
  simp_tac pure_ss [Abbr `s1`, Abbr `c1`] >>
  simp_tac (srw_ss()) [vfmContextTheory.context_fupdcanon,
    vfmContextTheory.execution_state_fupdcanon, vfmContextTheory.rollback_state_fupdcanon,
    vfmContextTheory.access_sets_fupdcanon, arithmeticTheory.ADD_ASSOC] >>
  simp_tac (srw_ss()) [vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
    combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ, vfmStateTheory.account_state_fupdcanon] >>
  `update_storage 1w 0w o update_storage 0w (n2w (w2n added+w2n excess-2)) o
     (if cnt+head = tail then update_storage 3w 0w o update_storage 2w 0w
      else update_storage 2w (cnt+head)) =
   (if cnt+head = tail then update_storage 3w 0w o update_storage 2w 0w
    else update_storage 2w (cnt+head)) o update_storage 1w 0w o
      update_storage 0w (n2w (w2n added+w2n excess-2))` by
    (Cases_on `cnt+head = tail` >>
     simp[FUN_EQ_THM, combinTheory.o_DEF, vfmStateTheory.update_storage_def,
       combinTheory.UPDATE_COMMUTES, wordsTheory.dimword_def]) >>
  simp[]
QED

Theorem withdrawal_return_prepare_run[local]:
  c.pc = 495 /\ c.stack = [cnt] /\ c.jumpDest = NONE /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  c.gasUsed+10 <= c.msgParams.gasLimit ==>
  run (s with contexts := (c,rb)::cs) = run (s with contexts :=
    (c with <|pc := 499; stack := [0w;76w*cnt]; gasUsed := c.gasUsed+10|>,rb)::cs)
Proof
  strip_tac >>
  `word_of_bytes F 0w [76w:byte] = (76w:bytes32)` by
    simp[byteTheory.word_of_bytes_def, byteTheory.set_byte_def,
      byteTheory.byte_index_def, byteTheory.word_slice_alt_zero] >>
  simp[SimpLHS, Q.INST [`n` |-> `1`, `ws` |-> `[76w:byte]`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`op` |-> `Mul`, `f` |-> `word_mul:bytes32 -> bytes32 -> bytes32`] system_binop_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    step_inst_def, is_call_def, static_gas_def, opcode_def] >>
  simp[SimpLHS, Q.INST [`n` |-> `0`, `ws` |-> `[]:byte list`] system_push_run,
    GSYM withdrawal_instruction_def, withdrawal_excess_parse, stack_limit_def,
    static_gas_def, opcode_def, byteTheory.word_of_bytes_def] >>
  simp[vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_return_run[local]:
  c.pc = 495 /\ c.stack = [n2w n] /\ c.jumpDest = NONE /\ n <= 16 /\
  c.msgParams.outputTo = empty_return_destination /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  buffer_length c.memory MOD 32 = 0 /\ 76*n <= buffer_length c.memory /\
  c.gasUsed+10 <= c.msgParams.gasLimit ==>
  run (s with contexts := [(c,rb)]) = SOME (INR NONE,
    s with contexts := [(c with <|pc := 499; stack := []; gasUsed := c.gasUsed+10;
      returnData := buffer_take 0 (76*n) c.memory|>,rb)])
Proof
  strip_tac >>
  `w2n (76w*n2w n:bytes32) = 76*n` by
    (simp[wordsTheory.word_mul_n2w, wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
     irule arithmeticTheory.MOD_UNIQUE >> qexists_tac `0` >> simp[]) >>
  drule_all withdrawal_return_prepare_run >>
  disch_then (qspecl_then [`s`, `rb`, `[]`] mp_tac) >> strip_tac >>
  qabbrev_tac `c1 = c with <|pc := 499; stack := [0w;76w*n2w n]; gasUsed := c.gasUsed+10|>` >>
  mp_tac (Q.INST [`c` |-> `c1`, `sz` |-> `76w*n2w n:bytes32`] queue_return_allocated_run) >>
  (impl_tac >- simp[Abbr `c1`, GSYM withdrawal_instruction_def, withdrawal_excess_parse]) >>
  gvs[Abbr `c1`, vfmContextTheory.context_fupdcanon]
QED

Theorem withdrawal_suffix_run[local]:
  c.pc = 387 /\ c.stack = [n2w n;n2w n;head;tail] /\ c.jumpDest = NONE /\
  ~c.msgParams.static /\ s.msdomain = Collect d /\ n <= 16 /\
  c.msgParams.outputTo = empty_return_destination /\
  c.msgParams.parsed = parse_code 0 FEMPTY withdrawal_request_code /\
  488 < LENGTH c.msgParams.code /\
  buffer_length c.memory MOD 32 = 0 /\ 76*n <= buffer_length c.memory /\
  excess = (if lookup_storage 0w (lookup_account c.msgParams.callee s.rollback.accounts).storage = -1w
    then 0w else lookup_storage 0w (lookup_account c.msgParams.callee s.rollback.accounts).storage) /\
  added = lookup_storage 1w (lookup_account c.msgParams.callee s.rollback.accounts).storage /\
  w2n added+w2n excess < dimword (:256) /\
  c.gasUsed+92744 <= c.msgParams.gasLimit ==>
  ?g ad su keys d'. g <= c.gasUsed+92744 /\
  run (s with contexts := [(c,rb)]) = SOME (INR NONE, s with <|
    contexts := [(c with <|pc := 499; stack := []; gasUsed := g;
      returnData := buffer_take 0 (76*n) c.memory;
      addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>,rb)];
    rollback := s.rollback with <|
      accounts := update_account c.msgParams.callee
        ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
          ((if head+n2w n = tail then update_storage 3w 0w o update_storage 2w 0w
            else update_storage 2w (head+n2w n)) o update_storage 1w 0w o
           update_storage 0w (n2w (w2n added+w2n excess-2)))) s.rollback.accounts;
      accesses := s.rollback.accesses with storageKeys := keys|>;
    msdomain := Collect d'|>)
Proof
  strip_tac >>
  `c.gasUsed+92734 <= c.msgParams.gasLimit` by decide_tac >>
  drule_all withdrawal_bookkeeping_run >>
  disch_then (qspecl_then [`rb`, `[]`] mp_tac) >>
  disch_then (qx_choosel_then [`g1`, `ad`, `su`, `keys`, `d1`] strip_assume_tac) >>
  qabbrev_tac `c1 = c with <|pc := 495; stack := [n2w n]; gasUsed := g1;
    addRefund := ad+c.addRefund; subRefund := su+c.subRefund|>` >>
  qabbrev_tac `s1 = s with <|rollback := s.rollback with <|
    accounts := update_account c.msgParams.callee
      ((lookup_account c.msgParams.callee s.rollback.accounts) with storage updated_by
        ((if head+n2w n = tail then update_storage 3w 0w o update_storage 2w 0w
          else update_storage 2w (head+n2w n)) o update_storage 1w 0w o
         update_storage 0w (n2w (w2n added+w2n excess-2)))) s.rollback.accounts;
    accesses := s.rollback.accesses with storageKeys := keys|>; msdomain := Collect d1|>` >>
  mp_tac (Q.INST [`c` |-> `c1`, `s` |-> `s1`] withdrawal_return_run) >>
  (impl_tac >- (simp[Abbr `c1`] >> decide_tac)) >>
  strip_tac >> qexistsl [`g1+10`, `ad`, `su`, `keys`, `d1`] >>
  conj_tac >- decide_tac >>
  gvs[Abbr `c1`, Abbr `s1`, vfmContextTheory.context_fupdcanon]
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
