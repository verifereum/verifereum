Theory vfmOriginalAccounts
Ancestors vfmExecution vfmContext vfmState vfmCompute vfmSettlement
Libs cv_transLib monadsyntax wordsLib

val () = monadsyntax.enable_monad "evm_execution";
val () = monadsyntax.enable_monadsyntax();

(* Exercise child execution and settlement without external fixtures. *)
Definition original_accounts_fixture_def:
  original_accounts_fixture =
    update_account 0x300w (empty_account_state with balance := 7) $
    update_account 0x200w (empty_account_state with balance := 100) $
    update_account 0x400w (empty_account_state with balance := 100) $
    settlement_accounts 10000000
End
val () = cv_auto_trans original_accounts_fixture_def;

Definition original_child_run_def:
  original_child_run nested gas code =
    case initial_state (Collect empty_domain) F 1 [] (settlement_block 0x500w)
      original_accounts_fixture (settlement_tx with gasLimit := 500000) of
      NONE => NONE
    | SOME s =>
      case (if nested then do
              consume_gas 200000;
              proceed_call Call 0x200w 0x400w 0 0 0 [] 200000
                empty_return_destination
            od else return ()) s of
        (INR _, _) => NONE
      | (INL (), s) =>
        case (do consume_gas gas;
                 proceed_create (if nested then 0x400w else 0x200w)
                   0x300w 0 code gas od) s of
          (INR _, _) => NONE
        | (INL (), s) => run_call s
End
val () = original_child_run_def
  |> SIMP_RULE std_ss [COND_RATOR, bind_def, ignore_bind_def]
  |> cv_auto_trans;

Definition original_accounts_observation_def:
  original_accounts_observation (result: unit execution_result option) =
    case result of
      NONE => NONE
    | SOME (r,s) =>
      case s.contexts of [] => NONE | (ctxt,_)::_ =>
      SOME (r, LENGTH s.contexts,
       lookup_storage 0w (lookup_account 0x300w s.originalAccounts).storage,
       account_empty (lookup_account 0x300w s.originalAccounts),
       lookup_storage 0w (lookup_account 0x300w s.rollback.accounts).storage,
       (lookup_account 0x300w s.rollback.accounts).nonce,
       (lookup_account 0x300w s.rollback.accounts).balance,
       ctxt.stack)
End
val () = cv_auto_trans original_accounts_observation_def;

Theorem original_storage_after_successful_create:
  original_accounts_observation
    (original_child_run F 100000 [0x60w; 9w; 0x60w; 0w; 0x55w; 0w]) =
  SOME (INL (), 1, 0w, T, 9w, 1, 7, [0x300w])
Proof
  CONV_TAC cv_eval
QED

Theorem original_accounts_survive_child_revert:
  original_accounts_observation
    (original_child_run F 100000
      [0x60w; 9w; 0x60w; 0w; 0x55w; 0x60w; 0w; 0x60w; 0w; 0xfdw]) =
  SOME (INL (), 1, 0w, T, 0w, 0, 7, [0w])
Proof
  CONV_TAC cv_eval
QED

Theorem original_accounts_survive_invalid_code_prefix:
  original_accounts_observation
    (original_child_run F 100000
      [0x60w; 9w; 0x60w; 0w; 0x55w;
       0x60w; 0xefw; 0x60w; 0w; 0x53w; 0x60w; 1w; 0x60w; 0w; 0xf3w]) =
  SOME (INL (), 1, 0w, T, 0w, 0, 7, [0w])
Proof
  CONV_TAC cv_eval
QED

Theorem original_accounts_survive_code_deposit_out_of_gas:
  original_accounts_observation
    (original_child_run F 100
      [0x60w; 0w; 0x60w; 0w; 0x53w; 0x60w; 1w; 0x60w; 0w; 0xf3w]) =
  SOME (INL (), 1, 0w, T, 0w, 0, 7, [0w])
Proof
  CONV_TAC cv_eval
QED

Definition original_enclosing_revert_def:
  original_enclosing_revert code =
    case original_child_run T 100000 code of
      SOME (INL (), s) => SOME (handle_step (SOME Reverted) s)
    | _ => NONE
End
val () = cv_auto_trans original_enclosing_revert_def;

Theorem original_accounts_survive_enclosing_call_revert:
  original_accounts_observation
    (original_enclosing_revert [0x60w; 9w; 0x60w; 0w; 0x55w; 0w]) =
  SOME (INL (), 1, 0w, T, 0w, 0, 7, [0w])
Proof
  CONV_TAC cv_eval
QED
