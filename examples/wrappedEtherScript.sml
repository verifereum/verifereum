open HolKernel boolLib bossLib Parse wordsLib
     combinTheory whileTheory
     vfmContextTheory vfmExecutionTheory vfmStateTheory vfmComputeTheory
     cv_transLib;

val () = new_theory "wrappedEther";

Definition valid_def:
  valid P f Q =
  ∀s: execution_state.
    P s ⇒ case f s : α execution_result
          of (r, t) => Q r t
End

Definition valid_result_def:
  valid_result P f Q =
  valid P f (λr s. ISL r ∧ Q (OUTL r) s)
End

Definition valid_result_fn_def:
  valid_result_fn P f Q g =
  valid_result P f (λr s. Q s ∧ r = g s)
End

Definition valid_result_eq_def:
  valid_result_eq P f Q x =
  valid_result_fn P f Q (K x)
End

Theorem valid_strengthen:
  valid P f Q1 ∧
  (∀r s. Q1 r s ⇒ Q r s)
  ⇒
  valid P f Q
Proof
  rw[valid_def]
  \\ last_x_assum drule \\ gvs[]
  \\ CASE_TAC \\ rw[]
QED

Theorem valid_result_valid:
  valid_result P f Q1 ∧
  (∀r s. ISL r ∧ Q1 (OUTL r) s ⇒ Q r s)
  ⇒
  valid P f Q
Proof
  rw[valid_result_def]
  \\ irule valid_strengthen
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem valid_result_eq_valid_result:
  valid_result_eq P f Q1 x ∧
  (∀s. Q1 s ⇒ Q x s)
  ⇒
  valid_result P f Q
Proof
  rw[valid_result_fn_def, valid_result_eq_def, valid_result_def]
  \\ irule valid_strengthen
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem valid_bind:
  valid_result P g Q1 ∧
  (∀x. valid (Q1 x) (f x) Q)
  ⇒
  valid P (monad_bind g f) Q
Proof
  rw[valid_result_def, valid_def, bind_def]
  \\ CASE_TAC \\ gvs[]
  \\ last_x_assum drule \\ rw[]
  \\ CASE_TAC \\ gvs[]
QED

Theorem valid_ignore_bind:
  valid_result P r Q1 ∧
  (∀x. valid (Q1 x) f Q)
  ⇒
  valid P (ignore_bind r f) Q
Proof
  rw[valid_def, valid_result_def, ignore_bind_def, bind_def]
  \\ first_x_assum drule
  \\ CASE_TAC \\ gvs[] \\ strip_tac
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem valid_result_bind:
  valid_result P g Q1 ∧
  (∀x. valid_result (Q1 x) (f x) Q)
  ⇒
  valid_result P (monad_bind g f) Q
Proof
  rw[]
  \\ rw[valid_result_def]
  \\ irule valid_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ irule valid_result_valid
  \\ qexists_tac`Q` \\ rw[]
QED

Theorem valid_result_ignore_bind:
  valid_result P r Q1 ∧
  (∀x. valid_result (Q1 x) f Q)
  ⇒
  valid_result P (ignore_bind r f) Q
Proof
  rw[]
  \\ rw[valid_result_def]
  \\ irule valid_ignore_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ irule valid_result_valid
  \\ qexists_tac`Q` \\ rw[]
QED

Theorem valid_result_get_current_context:
  (∀s. P s ⇒ ¬NULL s.contexts) ∧
  (∀s. P s ⇒ Q (HD s.contexts) s)
  ⇒
  valid_result P get_current_context Q
Proof
  rw[valid_result_def, valid_def, get_current_context_def]
  \\ rw[fail_def, return_def]
  \\ rpt(first_x_assum drule)
  \\ rw[]
QED

Theorem valid_result_eq_assert:
  (∀s. P s ⇒ b ∧ Q s)
  ⇒
  valid_result_eq P (assert b e) Q ()
Proof
  rw[valid_result_eq_def, valid_result_fn_def, valid_result_def, valid_def, assert_def]
QED

Theorem valid_result_eq_set_current_context:
  (∀s. P s ⇒ ¬NULL s.contexts) ∧
  (∀s. P s ⇒ Q (s with contexts updated_by λls. c :: TL ls))
  ⇒
  valid_result_eq P (set_current_context c) Q ()
Proof
  rw[valid_result_eq_def, valid_result_def, valid_def,
     valid_result_fn_def, set_current_context_def]
  \\ last_x_assum drule \\ rw[return_def]
  \\ last_x_assum drule \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`Q s1`
  \\ qmatch_asmsub_abbrev_tac`Q s2`
  \\ `s1 = s2` by rw[Abbr`s1`, Abbr`s2`, execution_state_component_equality]
  \\ rw[]
QED

Definition has_cc_def:
  has_cc P s =
  ∃c t. s.contexts = c :: t ∧ P c
End

Definition update_cc_def:
  update_cc f s =
  s with contexts updated_by (λls. (f (HD ls))::(TL ls))
End

Theorem valid_result_eq_consume_gas:
  (∀s. P s ⇒ has_cc (λc. c.gasUsed + n ≤ c.msgParams.gasLimit) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with gasUsed updated_by $+ n) s))
  ⇒
  valid_result_eq P (consume_gas n) Q ()
Proof
  rw[consume_gas_def]
  \\ rw[valid_result_eq_def, valid_result_fn_def]
  \\ irule valid_result_bind
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule valid_result_get_current_context
    \\ rw[] \\ res_tac \\ fs[has_cc_def])
  \\ irule valid_result_ignore_bind
  \\ qexists_tac`λr s. P s ∧ x = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule valid_result_eq_valid_result \\ rw[]
    \\ qexists_tac`λs. P s ∧ x = HD s.contexts` \\ rw[]
    \\ irule valid_result_eq_assert
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ irule valid_result_eq_valid_result
  \\ rw[]
  \\ qexists_tac`Q`
  \\ rw[]
  \\ irule valid_result_eq_set_current_context
  \\ rw[]
  \\ last_x_assum drule \\ rw[has_cc_def]
  \\ last_x_assum drule \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`Q s1`
  \\ qmatch_asmsub_abbrev_tac`Q s2`
  \\ `s1 = s2` by (
    rw[Abbr`s1`, Abbr`s2`, execution_state_component_equality,
       context_component_equality, update_cc_def] )
  \\ rw[]
QED

Theorem valid_result_eq_push_stack:
  (∀s. P s ⇒ has_cc (λc. LENGTH c.stack < stack_limit) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with stack updated_by CONS w) s))
  ⇒
  valid_result_eq P (push_stack w) Q ()
Proof
  (* TODO: mostly repeated from previous proof - abstract or automate? *)
  rw[push_stack_def, valid_result_eq_def, valid_result_fn_def, valid_result_def]
  \\ irule valid_bind \\ rw[]
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule valid_result_get_current_context
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ irule valid_ignore_bind \\ rw[]
  \\ qexists_tac`λr s. P s ∧ x = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule valid_result_eq_valid_result \\ rw[]
    \\ qexists_tac`λs. P s ∧ x = HD s.contexts` \\ rw[]
    \\ irule valid_result_eq_assert
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ irule valid_result_valid
  \\ rw[]
  \\ qexists_tac`λr s. Q s`
  \\ rw[]
  \\ irule valid_result_eq_valid_result
  \\ rw[]
  \\ qexists_tac`Q`
  \\ rw[]
  \\ irule valid_result_eq_set_current_context
  \\ rw[]
  \\ last_x_assum drule \\ rw[has_cc_def]
  \\ last_x_assum drule \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`Q s1`
  \\ qmatch_asmsub_abbrev_tac`Q s2`
  \\ `s1 = s2` by (
    rw[Abbr`s1`, Abbr`s2`, execution_state_component_equality,
       context_component_equality, update_cc_def] )
  \\ rw[]
QED

Theorem valid_result_eq_step_push:
  g = static_gas (Push n ws) ∧
  w = word_of_bytes F 0w (REVERSE ws) ∧
  (∀s. P s ⇒ has_cc (λc.
         c.gasUsed + g ≤ c.msgParams.gasLimit ∧
         LENGTH c.stack < stack_limit) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with <|
                  stack updated_by CONS w
                ; gasUsed updated_by $+ g |>) s))
  ⇒
  valid_result_eq P (step_push n ws) Q ()
Proof
  rw[step_push_def, valid_result_eq_def, valid_result_fn_def,
     valid_result_def, Excl"static_gas_def"]
  \\ qmatch_goalsub_abbrev_tac`consume_gas g`
  \\ qmatch_goalsub_abbrev_tac`push_stack w`
  \\ irule valid_ignore_bind \\ rw[]
  \\ qexists_tac`λr s. has_cc (λc. LENGTH c.stack < stack_limit) s ∧
                       Q (update_cc (λc. c with stack updated_by CONS w) s)`
  \\ reverse (rw[])
  >- (
    irule valid_result_eq_valid_result
    \\ qmatch_goalsub_abbrev_tac`_ ⇒ Q1 _ _`
    \\ qexists_tac`λs. Q1 () s`
    \\ rw[Abbr`Q1`]
    \\ irule valid_result_eq_consume_gas
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[update_cc_def]
    \\ last_x_assum drule \\ rw[update_cc_def]
    \\ qmatch_goalsub_abbrev_tac`Q s1`
    \\ qmatch_asmsub_abbrev_tac`Q s2`
    \\ `s1 = s2` by (
      rw[Abbr`s1`, Abbr`s2`, execution_state_component_equality,
         context_component_equality, update_cc_def] )
    \\ rw[])
  \\ irule valid_result_valid \\ rw[]
  \\ qexists_tac`λr s. Q s` \\ rw[]
  \\ irule valid_result_eq_valid_result
  \\ qexists_tac`Q` \\ rw[]
  \\ irule valid_result_eq_push_stack
  \\ rw[]
QED

Theorem valid_result_eq_inc_pc_or_jump_inc:
  n = LENGTH (opcode i) ∧ ¬is_call i ∧
  (∀s. P s ⇒ has_cc (λc. c.jumpDest = NONE) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with pc updated_by $+ n) s))
  ⇒
  valid_result_eq P (inc_pc_or_jump i) Q ()
Proof
  rw[valid_result_eq_def, inc_pc_or_jump_def,
     valid_result_fn_def, valid_result_def]
  \\ irule valid_bind
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ reverse conj_tac
  >- (
    irule valid_result_get_current_context
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ rw[]
  \\ reverse(Cases_on`x.jumpDest`)
  >- (
    rw[valid_def]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ gs[] )
  \\ rw[]
  \\ irule valid_result_valid \\ rw[]
  \\ qexists_tac`λr s. Q s`
  \\ rw[]
  \\ irule valid_result_eq_valid_result
  \\ rw[]
  \\ qexists_tac`Q`
  \\ rw[]
  \\ irule valid_result_eq_set_current_context
  \\ rw[]
  \\ last_x_assum drule \\ rw[has_cc_def]
  \\ last_x_assum drule \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`Q s1`
  \\ qmatch_asmsub_abbrev_tac`Q s2`
  \\ `s1 = s2` by (
    rw[Abbr`s1`, Abbr`s2`, execution_state_component_equality,
       context_component_equality, update_cc_def] )
  \\ rw[]
QED

Theorem valid_imp:
  valid P f Q ∧ P s
  ⇒
  ∃r t. f s = (r, t) ∧ Q r t
Proof
  rw[valid_def]
  \\ last_x_assum drule
  \\ CASE_TAC \\ rw[]
QED

Definition Keccak_256_string_def:
  Keccak_256_string s =
  Keccak_256_w64 $ MAP (n2w o ORD) s
End

val () = cv_auto_trans Keccak_256_string_def;

(*
Theorem initial_state_contexts:
  initial_state c ph bk ms tx = SOME s ⇒
  s.contexts = [
    apply_intrinsic_cost tx.accessList
      (initial_context (callee_from_tx_to tx.from tx.nonce tx.to)
*)

Definition deploy_data_def:
  deploy_data = REVERSE $ hex_to_rev_bytes [] $
  "60606040526040805190810160405280600d81526020017f57726170706564204574686572000000000000000000000000000000000000008152506000908051906020019061004f9291906100c8565b506040805190810160405280600481526020017f57455448000000000000000000000000000000000000000000000000000000008152506001908051906020019061009b9291906100c8565b506012600260006101000a81548160ff021916908360ff16021790555034156100c357600080fd5b61016d565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f1061010957805160ff1916838001178555610137565b82800160010185558215610137579182015b8281111561013657825182559160200191906001019061011b565b5b5090506101449190610148565b5090565b61016a91905b8082111561016657600081600090555060010161014e565b5090565b90565b610c348061017c6000396000f3006060604052600436106100af576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806306fdde03146100b9578063095ea7b31461014757806318160ddd146101a157806323b872dd146101ca5780632e1a7d4d14610243578063313ce5671461026657806370a082311461029557806395d89b41146102e2578063a9059cbb14610370578063d0e30db0146103ca578063dd62ed3e146103d4575b6100b7610440565b005b34156100c457600080fd5b6100cc6104dd565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561010c5780820151818401526020810190506100f1565b50505050905090810190601f1680156101395780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561015257600080fd5b610187600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061057b565b604051808215151515815260200191505060405180910390f35b34156101ac57600080fd5b6101b461066d565b6040518082815260200191505060405180910390f35b34156101d557600080fd5b610229600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061068c565b604051808215151515815260200191505060405180910390f35b341561024e57600080fd5b61026460048080359060200190919050506109d9565b005b341561027157600080fd5b610279610b05565b604051808260ff1660ff16815260200191505060405180910390f35b34156102a057600080fd5b6102cc600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610b18565b6040518082815260200191505060405180910390f35b34156102ed57600080fd5b6102f5610b30565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561033557808201518184015260208101905061031a565b50505050905090810190601f1680156103625780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561037b57600080fd5b6103b0600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610bce565b604051808215151515815260200191505060405180910390f35b6103d2610440565b005b34156103df57600080fd5b61042a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610be3565b6040518082815260200191505060405180910390f35b34600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055503373ffffffffffffffffffffffffffffffffffffffff167fe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c346040518082815260200191505060405180910390a2565b60008054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156105735780601f1061054857610100808354040283529160200191610573565b820191906000526020600020905b81548152906001019060200180831161055657829003601f168201915b505050505081565b600081600460003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a36001905092915050565b60003073ffffffffffffffffffffffffffffffffffffffff1631905090565b600081600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101515156106dc57600080fd5b3373ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff16141580156107b457507fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205414155b156108cf5781600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015151561084457600080fd5b81600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055505b81600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600360008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190509392505050565b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410151515610a2757600080fd5b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055503373ffffffffffffffffffffffffffffffffffffffff166108fc829081150290604051600060405180830381858888f193505050501515610ab457600080fd5b3373ffffffffffffffffffffffffffffffffffffffff167f7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65826040518082815260200191505060405180910390a250565b600260009054906101000a900460ff1681565b60036020528060005260406000206000915090505481565b60018054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015610bc65780601f10610b9b57610100808354040283529160200191610bc6565b820191906000526020600020905b815481529060010190602001808311610ba957829003601f168201915b505050505081565b6000610bdb33848461068c565b905092915050565b60046020528160005260406000206020528060005260406000206000915091505054815600a165627a7a72305820deb4c2ccab3c2fdca32ab3f46728389c2fe2c165d5fafa07661e4e004f6c344a0029"
End

val () = cv_trans_deep_embedding EVAL deploy_data_def;

Definition deploy_tx_def:
  deploy_tx = <|
    from := 0x4F26FfBe5F04ED43630fdC30A87638d53D0b0876w
  ; to := NONE
  ; data := deploy_data
  ; nonce := 446
  ; value := 0
  ; gasLimit := 1500000
  ; gasPrice := 21000000000
  ; accessList := []
  |>
End

val () = cv_auto_trans deploy_tx_def;

Definition deploy_block_def:
  deploy_block = <|
    baseFeePerGas := 0 (* fake *)
  ; number := 4719568
  ; timeStamp := 1513077455
  ; coinBase := 0x829BD824B016326A401d083B33D092293333A830w
  ; gasLimit := 7967026
  ; prevRandao := 0w (* fake *)
  ; hash := 0xd6e5f60d6b2367e74cd2aa520dbeb104826c3932eb482cc16e7f7ef5f8f74799w
  ; parentBeaconBlockRoot := 0w (* fake *)
  ; transactions := [deploy_tx] (* not true, many others *)
  |>
End

val () = cv_auto_trans deploy_block_def;

Definition deploy_accounts_def:
  deploy_accounts =
  update_account (deploy_tx.from)
  <| nonce := 446
   ; balance := 3508132013219893088
   ; storage := empty_storage
   ; code := []
   |>
  empty_accounts (* not accurate, many others *)
End

val () = cv_auto_trans deploy_accounts_def;

Definition deploy_tx_result_def:
  deploy_tx_result =
    run_transaction_with_fuel 267 1 [] deploy_block deploy_accounts deploy_tx
End

val () = cv_auto_trans deploy_tx_result_def;

Definition contract_code_def:
  contract_code = REVERSE $ hex_to_rev_bytes [] $
  "6060604052600436106100af576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806306fdde03146100b9578063095ea7b31461014757806318160ddd146101a157806323b872dd146101ca5780632e1a7d4d14610243578063313ce5671461026657806370a082311461029557806395d89b41146102e2578063a9059cbb14610370578063d0e30db0146103ca578063dd62ed3e146103d4575b6100b7610440565b005b34156100c457600080fd5b6100cc6104dd565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561010c5780820151818401526020810190506100f1565b50505050905090810190601f1680156101395780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561015257600080fd5b610187600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061057b565b604051808215151515815260200191505060405180910390f35b34156101ac57600080fd5b6101b461066d565b6040518082815260200191505060405180910390f35b34156101d557600080fd5b610229600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061068c565b604051808215151515815260200191505060405180910390f35b341561024e57600080fd5b61026460048080359060200190919050506109d9565b005b341561027157600080fd5b610279610b05565b604051808260ff1660ff16815260200191505060405180910390f35b34156102a057600080fd5b6102cc600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610b18565b6040518082815260200191505060405180910390f35b34156102ed57600080fd5b6102f5610b30565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561033557808201518184015260208101905061031a565b50505050905090810190601f1680156103625780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561037b57600080fd5b6103b0600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610bce565b604051808215151515815260200191505060405180910390f35b6103d2610440565b005b34156103df57600080fd5b61042a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610be3565b6040518082815260200191505060405180910390f35b34600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055503373ffffffffffffffffffffffffffffffffffffffff167fe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c346040518082815260200191505060405180910390a2565b60008054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156105735780601f1061054857610100808354040283529160200191610573565b820191906000526020600020905b81548152906001019060200180831161055657829003601f168201915b505050505081565b600081600460003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a36001905092915050565b60003073ffffffffffffffffffffffffffffffffffffffff1631905090565b600081600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101515156106dc57600080fd5b3373ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff16141580156107b457507fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205414155b156108cf5781600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015151561084457600080fd5b81600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055505b81600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600360008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190509392505050565b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410151515610a2757600080fd5b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055503373ffffffffffffffffffffffffffffffffffffffff166108fc829081150290604051600060405180830381858888f193505050501515610ab457600080fd5b3373ffffffffffffffffffffffffffffffffffffffff167f7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65826040518082815260200191505060405180910390a250565b600260009054906101000a900460ff1681565b60036020528060005260406000206000915090505481565b60018054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015610bc65780601f10610b9b57610100808354040283529160200191610bc6565b820191906000526020600020905b815481529060010190602001808311610ba957829003601f168201915b505050505081565b6000610bdb33848461068c565b905092915050565b60046020528160005260406000206020528060005260406000206000915091505054815600a165627a7a72305820deb4c2ccab3c2fdca32ab3f46728389c2fe2c165d5fafa07661e4e004f6c344a0029"
End

val () = cv_trans_deep_embedding EVAL contract_code_def;

Theorem deploy_produces_correct_code_and_address:
  ∃res ms.
    deploy_tx_result = SOME ((res, ms), 0) ∧
    res.result = NONE ∧
    let acc = lookup_account 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2w ms  in
    acc.nonce = 1 ∧
    acc.balance = 0 ∧
    (* acc.storage = TODO ∧ *)
    acc.code = contract_code
Proof
  CONV_TAC(STRIP_QUANT_CONV(PATH_CONV "lrlr" cv_eval))
  \\ qmatch_goalsub_abbrev_tac`SOME ((res, ms), _)`
  \\ qexistsl_tac[`res`,`ms`]
  \\ conj_tac >- rw[]
  \\ conj_tac >- rw[Abbr`res`]
  \\ rewrite_tac[lookup_account_def]
  \\ qunabbrev_tac`ms`
  \\ rewrite_tac[APPLY_UPDATE_THM]
  \\ rewrite_tac[LET_DEF]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ IF_CASES_TAC >- (pop_assum mp_tac \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac)
  \\ IF_CASES_TAC >- (pop_assum mp_tac \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac)
  \\ conj_tac >- rw[]
  \\ conj_tac >- rw[]
  (* \\ conj_tac >- ( rw[] ) *)
  \\ rewrite_tac[account_state_accessors]
  \\ CONV_TAC (RAND_CONV cv_eval)
  \\ CONV_TAC (listLib.list_EQ_CONV EVAL)
QED

(*
[{"constant":true,"inputs":[],"name":"name","outputs":[{"name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},
{"constant":false,"inputs":[{"name":"guy","type":"address"},{"name":"wad","type":"uint256"}],"name":"approve","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},
{"constant":true,"inputs":[],"name":"totalSupply","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},
{"constant":false,"inputs":[{"name":"src","type":"address"},{"name":"dst","type":"address"},{"name":"wad","type":"uint256"}],"name":"transferFrom","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},
{"constant":false,"inputs":[{"name":"wad","type":"uint256"}],"name":"withdraw","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},
{"constant":true,"inputs":[],"name":"decimals","outputs":[{"name":"","type":"uint8"}],"payable":false,"stateMutability":"view","type":"function"},
{"constant":true,"inputs":[{"name":"","type":"address"}],"name":"balanceOf","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},
{"constant":true,"inputs":[],"name":"symbol","outputs":[{"name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},
{"constant":false,"inputs":[{"name":"dst","type":"address"},{"name":"wad","type":"uint256"}],"name":"transfer","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},
{"constant":false,"inputs":[],"name":"deposit","outputs":[],"payable":true,"stateMutability":"payable","type":"function"},
{"constant":true,"inputs":[{"name":"","type":"address"},{"name":"","type":"address"}],"name":"allowance","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},
{"payable":true,"stateMutability":"payable","type":"fallback"},
{"anonymous":false,"inputs":[{"indexed":true,"name":"src","type":"address"},{"indexed":true,"name":"guy","type":"address"},{"indexed":false,"name":"wad","type":"uint256"}],"name":"Approval","type":"event"},
{"anonymous":false,"inputs":[{"indexed":true,"name":"src","type":"address"},{"indexed":true,"name":"dst","type":"address"},{"indexed":false,"name":"wad","type":"uint256"}],"name":"Transfer","type":"event"},
{"anonymous":false,"inputs":[{"indexed":true,"name":"dst","type":"address"},{"indexed":false,"name":"wad","type":"uint256"}],"name":"Deposit","type":"event"},
{"anonymous":false,"inputs":[{"indexed":true,"name":"src","type":"address"},{"indexed":false,"name":"wad","type":"uint256"}],"name":"Withdrawal","type":"event"}]
*)

Definition abi_signatures_def:
  abi_signatures = [
    "name()";
    "approve(address,uint256)";
    "totalSupply()";
    "transferFrom(address,address,uint256)";
    "withdraw(uint256)";
    "decimals()";
    "balanceOf(address)";
    "symbol()";
    "transfer(address,uint256)";
    "deposit()";
    "allowance(address,address)"
  ]
End

val () = cv_trans_deep_embedding EVAL abi_signatures_def;

Definition MAP_TAKE_4_Keccak_256_string_def:
  MAP_TAKE_4_Keccak_256_string ls = MAP (TAKE 4 o Keccak_256_string) ls
End

val () = cv_auto_trans MAP_TAKE_4_Keccak_256_string_def;

Definition abi_4bytes_def:
  abi_4bytes = MAP_TAKE_4_Keccak_256_string abi_signatures
End

val () = cv_auto_trans (abi_4bytes_def |> CONV_RULE (RAND_CONV cv_eval))

Theorem contract_code_eq = cv_eval “contract_code”;

Definition parsed_contract_code_def:
  parsed_contract_code = parse_code 0 FEMPTY contract_code
End

Theorem parsed_contract_code_eq =
  parsed_contract_code_def
  |> CONV_RULE(RAND_CONV cv_eval);

val () = cv_auto_trans parsed_contract_code_eq;

Theorem FLOOKUP_parsed_contract_code_0 =
  cv_eval “FLOOKUP parsed_contract_code 0”;

(*
Theorem call_follows_abi_4bytes:
  tx.to = SOME addr ∧
  (lookup_account addr ms).code = contract_code ∧
  run_transaction 1 ph bk ms tx = SOME (res, ms2) ∧
  res.result ≠ SOME Reverted ∧ res.result ≠ SOME OutOfGas
  ⇒
  ∃sel.
    sel ∈ set abi_4bytes ∧
    sel ≼ tx.data
Proof
  rw[run_transaction_def, run_create_def]
  \\ gvs[CaseEq"option", CaseEq"prod", CaseEq"sum"]
  \\ qhdtm_x_assum `run` mp_tac
  \\ simp[run_def]
  \\ simp[Once OWHILE_THM]
  \\ qmatch_goalsub_abbrev_tac`OWHILE _ f`
  \\ simp[Once step_def]
  \\ simp[handle_def]
  \\ `s.contexts <> []` by gvs[initial_state_def, CaseEq"option"]
  \\ simp[Once bind_def, get_current_context_def, return_def]
  \\ qhdtm_x_assum`initial_state`mp_tac
  \\ simp[initial_state_def, CaseEq"option"]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`[ctxt]`
  \\ gvs[]
  \\ `ctxt.msgParams.code = contract_code ∧ ctxt.pc = 0`
  by gvs[Abbr`ctxt`, apply_intrinsic_cost_def,
         initial_msg_params_def, code_from_tx_def]
  \\ gvs[]
  \\ IF_CASES_TAC
  >- ( pop_assum mp_tac \\ rewrite_tac[contract_code_eq] \\ rw[] )
  \\ `ctxt.msgParams.parsed = parsed_contract_code`
  by gvs[Abbr`ctxt`, apply_intrinsic_cost_def, initial_msg_params_def,
         parsed_contract_code_def]
  \\ simp[FLOOKUP_parsed_contract_code_0]
  \\ simp[step_inst_def]
  \\ qmatch_goalsub_abbrev_tac`pair_CASE (_ s)`
  \\ qmatch_goalsub_abbrev_tac`g s`
  \\ `valid_result_eq ((=) s) g ((=) (update_cc uu s)) ()`
  by (
    qunabbrev_tac`g`
*)

val () = export_theory();
