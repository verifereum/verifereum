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
   ; callData    : byte list
   |>
End

Datatype:
  context =
  <| stack      : bytes32 list
   ; memory     : num -> bytes32
   ; pc         : num
   ; returnData : byte list
   ; gasUsed    : num
   ; gasLeft    : num
   ; logs       : event list
   ; accAddress : address set
   ; accStorage : (address # bytes32) set
   ; callParams : call_parameters
   ; txParams   : transaction_parameters
   |>
End

Definition wf_context_def:
  wf_context c ⇔
    LENGTH c.stack ≤ 1024
End

Datatype:
  transaction_state =
  <| contexts : context list
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
  initial_context b t =
  <| stack      := []
   ; memory     := K 0w
   ; pc         := 0
   ; returnData := []
   ; gasUsed    := 0
   ; gasLeft    := t.gasLimit
   ; logs       := []
   ; accAddress := IMAGE (λe. e.account) (set t.accessList)
   ; accStorage := BIGUNION
                     (IMAGE (λe. IMAGE (λk. (e.account, k)) e.keys)
                            (set t.accessList))
   ; callParams := initial_call_params t
   ; txParams   := initial_tx_params b t
   |>
End

val _ = export_theory();
