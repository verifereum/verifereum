open HolKernel boolLib bossLib Parse
     pred_setTheory finite_mapTheory
     vfmTypesTheory vfmStateTheory vfmTransactionTheory vfmOperationTheory;

val _ = new_theory "vfmContext";

Datatype:
  transaction_parameters =
  <| origin         : address
   ; gasPrice       : num
   ; baseFee        : num
   ; blockNumber    : num
   ; blockTimeStamp : num
   ; blockCoinBase  : address
   ; blockGasLimit  : num
   ; prevRandao     : bytes32
   ; chainId        : num
   |>
End

Datatype:
  access_sets =
  <| addresses   : address set
   ; storageKeys : (address # bytes32) set
   |>
End

Datatype:
  memory_range =
  <| offset : num
   ; size   : num
   |>
End

Datatype:
  return_destination =
  | Memory memory_range
  | Code address
End

Datatype:
  call_parameters =
  <| caller    : address
   ; callee    : address
   ; code      : byte list
   ; value     : num
   ; static    : bool
   ; gasLimit  : num
   ; data      : byte list
   ; outputTo  : return_destination
   (* values at the start of the call, for rollback *)
   ; accounts  : evm_accounts
   ; accesses  : access_sets
   |>
End

Datatype:
  context =
  <| stack      : bytes32 list
   ; memory     : byte list
   ; pc         : num
   ; jumpDest   : num option
   ; returnData : byte list
   ; gasUsed    : num
   ; gasRefund  : num
   ; logs       : event list
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
   ; accesses : access_sets
   ; accounts : evm_accounts
   |>
End

Datatype:
  block =
  <| baseFee    : num
   ; number     : num
   ; timeStamp  : num
   ; coinBase   : address
   ; gasLimit   : num
   ; prevRandao : bytes32
   |>
End

Datatype:
  call_context =
  <| code      : byte list
   ; accounts  : evm_accounts
   ; accesses  : access_sets
   ; outputTo  : return_destination
   ; static    : bool
   |>
End

Definition initial_call_params_def:
  initial_call_params ctxt t =
  <| caller    := t.from
   ; callee    := t.to
   ; code      := ctxt.code
   ; value     := t.value
   ; static    := ctxt.static
   ; data      := t.data
   ; gasLimit  := t.gasLimit
   ; accounts  := ctxt.accounts
   ; accesses  := ctxt.accesses
   ; outputTo  := ctxt.outputTo
   |>
End

Definition initial_tx_params_def:
  initial_tx_params c b t =
  <| origin         := t.from
   ; gasPrice       := t.gasPrice
   ; baseFee        := b.baseFee
   ; blockNumber    := b.number
   ; blockTimeStamp := b.timeStamp
   ; blockCoinBase  := b.coinBase
   ; blockGasLimit  := b.gasLimit
   ; prevRandao     := b.prevRandao
   ; chainId        := c
   |>
End

Definition initial_context_def:
  initial_context ctxt t =
  <| stack      := []
   ; memory     := []
   ; pc         := 0
   ; jumpDest   := NONE
   ; returnData := []
   ; gasUsed    := 0
   ; gasRefund  := 0
   ; logs       := []
   ; callParams := initial_call_params ctxt t
   |>
End

Theorem initial_context_simp[simp]:
  (initial_context ctxt t).stack = []
Proof
  rw[initial_context_def]
  (* TODO: add more if needed *)
QED

Theorem wf_initial_context[simp]:
  wf_context (initial_context ctxt t)
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

Definition initial_access_sets_def:
  initial_access_sets t =
  <| addresses   := IMAGE (λe. e.account) (set t.accessList)
   ; storageKeys := BIGUNION
                      (IMAGE (λe. IMAGE (λk. (e.account, k)) e.keys)
                             (set t.accessList))
   |>
End

Definition initial_state_def:
  initial_state c a b r t =
  let acc = initial_access_sets t in
  let ctxt = <| code := (a t.to).code; accounts := a; accesses := acc
              ; outputTo := r; static := F |> in
  <| contexts := [initial_context ctxt t]
   ; txParams := initial_tx_params c b t
   ; accesses := acc
   ; accounts := a (* TODO: transfer t.value if needed? *)
   |>
End

Theorem initial_state_simp[simp]:
    (initial_state c a b r t).accounts = a
  ∧ (initial_state c a b r t).accesses = initial_access_sets t
  ∧ (initial_state c a b r t).txParams = initial_tx_params c b t
Proof
  rw[initial_state_def]
QED

Theorem wf_initial_state[simp]:
  wf_accounts a ⇒
  wf_state (initial_state c a b r t)
Proof
  rw[wf_accounts_def, wf_state_def]
  \\ rw[initial_state_def]
QED

val _ = export_theory();
