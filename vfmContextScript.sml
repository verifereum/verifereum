open HolKernel boolLib bossLib Parse
     listTheory rich_listTheory pred_setTheory finite_setTheory
     vfmTypesTheory vfmStateTheory vfmTransactionTheory vfmOperationTheory;

val _ = new_theory "vfmContext";

Datatype:
  transaction_parameters =
  <| origin         : address
   ; gasPrice       : num
   ; baseFeePerGas  : num
   ; blockNumber    : num
   ; blockHash      : bytes32
   ; blockTimeStamp : num
   ; blockCoinBase  : address
   ; blockGasLimit  : num
   ; prevRandao     : bytes32
   ; chainId        : num
   |>
End

Datatype:
  storage_key = SK address bytes32
End

Datatype:
  access_sets =
  <| addresses   : address fset
   ; storageKeys : storage_key fset
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
   ; parsed    : num |-> opname
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
  stack_limit = 1024n
End

Definition context_limit_def[simp]:
  context_limit = 1024n
End

Definition wf_context_def:
  wf_context c ⇔
    LENGTH c.stack ≤ stack_limit
End

Datatype:
  execution_state =
  <| contexts : context list
   ; txParams : transaction_parameters
   ; accesses : access_sets
   ; accounts : evm_accounts
   |>
End

Datatype:
  block =
  <| baseFeePerGas         : num
   ; number                : num
   ; timeStamp             : num
   ; coinBase              : address
   ; gasLimit              : num
   ; prevRandao            : bytes32
   ; hash                  : bytes32
   ; parentBeaconBlockRoot : bytes32
   ; transactions          : transaction list
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

Definition base_cost_def:
  base_cost = 21000n
End

Definition call_data_cost_def:
  call_data_cost is_zero =
  if is_zero then 4n else 16
End

Definition intrinsic_cost_def:
  intrinsic_cost (data: byte list) =
  base_cost + SUM (MAP (λb. call_data_cost (b = 0w)) data)
End

Definition parse_code_def:
  parse_code pc m code =
  if NULL code then m else
  case parse_opcode code of
  | NONE => m
  | SOME op =>
    let n = LENGTH $ opcode op in
    parse_code (pc + n) (m |+ (pc, op)) (DROP n code)
Termination
  WF_REL_TAC`measure (LENGTH o SND o SND)`
  \\ rw[LENGTH_DROP, LENGTH_NOT_NULL]
End

Definition initial_call_params_def:
  initial_call_params ctxt t =
  <| caller    := t.from
   ; callee    := t.to
   ; code      := ctxt.code
   ; parsed    := parse_code 0 FEMPTY ctxt.code
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
   ; baseFeePerGas  := b.baseFeePerGas
   ; blockNumber    := b.number
   ; blockHash      := b.hash
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

Theorem initial_call_params_simp[simp]:
  (initial_call_params ctxt t).code = ctxt.code ∧
  (initial_call_params ctxt t).gasLimit = t.gasLimit ∧
  (initial_call_params ctxt t).outputTo = ctxt.outputTo
  (* TODO: as needed *)
Proof
  rw[initial_call_params_def]
QED

Theorem initial_context_simp[simp]:
  (initial_context ctxt t).stack = [] ∧
  (initial_context ctxt t).memory = [] ∧
  (initial_context ctxt t).pc = 0 ∧
  (initial_context ctxt t).jumpDest = NONE ∧
  (initial_context ctxt t).returnData = [] ∧
  (initial_context ctxt t).gasUsed = 0 ∧
  (initial_context ctxt t).gasRefund = 0 ∧
  (initial_context ctxt t).logs = [] ∧
  (initial_context ctxt t).callParams = initial_call_params ctxt t
Proof
  rw[initial_context_def]
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
  <| addresses   := fIMAGE (λe. e.account) (fset_ABS t.accessList)
   ; storageKeys := fBIGUNION
                      (fIMAGE (λe. fIMAGE (SK e.account) e.keys)
                              (fset_ABS t.accessList))
   |>
End

Definition apply_intrinsic_cost_def:
  apply_intrinsic_cost c =
  c with callParams updated_by (λp.
    p with gasLimit updated_by (λl.
      l - intrinsic_cost p.data
    )
  )
End

Theorem wf_context_apply_intrinsic_cost[simp]:
  wf_context (apply_intrinsic_cost c) =
  wf_context c
Proof
  rw[apply_intrinsic_cost_def, wf_context_def]
QED

Definition initial_state_def:
  initial_state c a b r t =
  let sender = (a t.from) in
  let fee = t.gasLimit * t.gasPrice in (* TODO: add blob gas fee *)
  if sender.nonce ≠ t.nonce ∨ t.nonce ≥ 2 ** 64 - 1 then NONE else
  if sender.balance < fee + t.value then NONE else
  let updatedSender = sender with <|
    nonce := SUC sender.nonce;
    balance := sender.balance - fee
  |> in
  let accounts = (t.from =+ updatedSender) a in
  let acc = initial_access_sets t in
  let ctxt = <| code := (a t.to).code; accounts := accounts; accesses := acc
              ; outputTo := r; static := F |> in
  SOME $
  <| contexts := [apply_intrinsic_cost $ initial_context ctxt t]
   ; txParams := initial_tx_params c b t
   ; accesses := acc
   ; accounts := accounts
   |>
End

Theorem wf_initial_state:
  wf_accounts a ∧ initial_state c a b r t = SOME s
  ⇒
  wf_state s
Proof
  rw[wf_accounts_def, wf_state_def, initial_state_def] \\ rw[]
  \\ gs[wf_account_state_def, combinTheory.APPLY_UPDATE_THM]
  \\ rw[]
QED

val _ = export_theory();
