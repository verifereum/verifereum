open HolKernel boolLib bossLib Parse
     pred_setTheory finite_mapTheory
     vfmTypesTheory vfmStateTheory vfmTransactionTheory vfmOperationTheory;

val _ = new_theory "vfmContext";

Datatype:
  transaction_parameters =
  <| origin      : address
   ; gasPrice    : num
   ; baseFee     : num
   ; blockNumber : num
   ; prevRandao  : bytes32
   |>
End

Datatype:
  call_parameters =
  <| caller      : address
   ; callee      : address
   ; value       : num
   ; gasLimit    : num
   ; callData    : byte list
   |>
End

Datatype:
  context =
  <| stack      : bytes32 list
   ; memory     : num |-> bytes32
   ; pc         : num
   ; returnData : byte list
   ; gasUsed    : num
   ; gasRefund  : num
   ; logs       : event list
   ; accAddress : address set
   ; accStorage : (address # bytes32) set
   ; callParams : call_parameters
   |>
End

Definition stack_limit_def[simp]:
  stack_limit = 1024
End

Definition context_limit_def[simp]:
  context_limit = 1024
End

Definition wf_context_def:
  wf_context c ⇔
    LENGTH c.stack ≤ stack_limit
End

Datatype:
  transaction_state =
  <| contexts : context list
   ; txParams : transaction_parameters
   ; accounts : evm_accounts
   |>
End

Datatype:
  block =
  <| baseFee    : num
   ; number     : num
   ; timeStamp  : num
   ; prevRandao : bytes32
   |>
End

Definition initial_call_params_def:
  initial_call_params t =
  <| caller   := t.from
   ; callee   := t.to
   ; value    := t.value
   ; callData := t.data
   ; gasLimit := t.gasLimit
   |>
End

Definition initial_tx_params_def:
  initial_tx_params b t =
  <| origin      := t.from
   ; gasPrice    := t.gasPrice
   ; baseFee     := b.baseFee
   ; blockNumber := b.number
   ; prevRandao  := b.prevRandao
   |>
End

Definition initial_context_def:
  initial_context t =
  <| stack      := []
   ; memory     := FEMPTY
   ; pc         := 0
   ; returnData := []
   ; gasUsed    := 0
   ; gasRefund  := 0
   ; logs       := []
   ; accAddress := IMAGE (λe. e.account) (set t.accessList)
   ; accStorage := BIGUNION
                     (IMAGE (λe. IMAGE (λk. (e.account, k)) e.keys)
                            (set t.accessList))
   ; callParams := initial_call_params t
   |>
End

Theorem initial_context_simp[simp]:
  (initial_context t).stack = []
Proof
  rw[initial_context_def]
  (* TODO: add more if needed *)
QED

Theorem wf_initial_context[simp]:
  wf_context (initial_context t)
Proof
  rw[wf_context_def]
QED

Definition wf_state_def:
  wf_state s ⇔
    s.contexts ≠ [] ∧
    LENGTH s.contexts ≤ context_limit ∧
    EVERY wf_context s.contexts ∧
    wf_accounts s.accounts
End

Definition initial_state_def:
  initial_state a b t =
  <| contexts := [initial_context t]
   ; txParams := initial_tx_params b t
   ; accounts := a
   |>
End

Theorem initial_state_simp[simp]:
  (initial_state a b t).contexts = [initial_context t] ∧
  (initial_state a b t).accounts = a ∧
  (initial_state a b t).txParams = initial_tx_params b t
Proof
  rw[initial_state_def]
QED

Theorem wf_initial_state[simp]:
  wf_accounts a ⇒
  wf_state (initial_state a b t)
Proof
  rw[wf_accounts_def, wf_state_def]
QED

val _ = export_theory();
