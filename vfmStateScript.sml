open HolKernel boolLib bossLib Parse
     wordsTheory
     vfmTypesTheory;

val _ = new_theory "vfmState";

Type storage = “:bytes32 -> bytes32”;

Datatype:
  account_state =
  <| nonce   : num
   ; balance : num
   ; storage : storage
   ; code    : byte list
   |>
End

Definition empty_storage_def:
  empty_storage: bytes32 -> bytes32 = K 0w
End

(* TODO: this probably needs to depend on block number (for hardforks) *)
Definition wf_account_state_def:
  wf_account_state a
  ⇔ a.nonce < 2 ** 64                  (* https://eips.ethereum.org/EIPS/eip-2681 *)
  ∧ LENGTH a.code <= 2 ** 14 + 2 ** 13 (* https://eips.ethereum.org/EIPS/eip-170 *)
End

Definition empty_account_state_def:
  empty_account_state =
    <| nonce := 0
     ; balance := 0
     ; storage := empty_storage
     ; code := []
     |>
End

Theorem wf_empty_account_state[simp]:
  wf_account_state empty_account_state
Proof
  rw[empty_account_state_def, wf_account_state_def]
QED

Type evm_accounts = “:address -> account_state”

Definition wf_accounts_def:
  wf_accounts a ⇔ ∀x. wf_account_state (a x)
End

val _ = export_theory();
