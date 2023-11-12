open HolKernel boolLib bossLib Parse
     wordsTheory finite_mapTheory
     vfmTypesTheory;

val _ = new_theory "vfmState";

Datatype:
  account_state =
  <| nonce   : num
   ; balance : num
   ; storage : bytes32 |-> bytes32
   ; code    : byte list
   |>
End

(* TODO: this probably needs to depend on block number (for hardforks) *)
Definition wf_account_state_def:
  wf_account_state a
  ⇔ a.nonce < 2 ** 64                  (* https://eips.ethereum.org/EIPS/eip-2681 *)
  ∧ LENGTH a.code <= 2 ** 14 + 2 ** 13 (* https://eips.ethereum.org/EIPS/eip-170 *)
End

Type evm_accounts = “:address -> account_state”

Definition wf_accounts_def:
  wf_accounts a ⇔ ∀x. wf_account_state (a x)
End

val _ = export_theory();
