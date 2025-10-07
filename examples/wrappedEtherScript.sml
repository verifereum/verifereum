Theory wrappedEther
Ancestors
  arithmetic byte list rich_list combin
  vfmOperation vfmConstants vfmState vfmExecution vfmCompute
  set_sep prog vfmProg
Libs
  cv_transLib wordsLib blastLib helperLib
  intLib

Theorem NOT_LENGTH_ADD_LEQ:
  ¬(LENGTH ls + n ≤ n) ⇔ ls ≠ []
Proof
  Cases_on`ls` \\ rw[]
QED

val MULT_32_word_size_32 =
  cv_eval “32 * word_size 32”

val MULT_32_word_size_64 =
  cv_eval “32 * word_size 64”

val MULT_32_word_size_96 =
  cv_eval “32 * word_size 96”

val MULT_32_word_size_128 =
  cv_eval “32 * word_size 128”

Theorem memory_cost_change:
  (LENGTH m2 = LENGTH m1) ∧
  (o2 + z2 = o1 + z1) ∧
  ((z2 = 0) = (z1 = 0))
  ⇒
  memory_cost m1 o1 z1 = memory_cost m2 o2 z2
Proof
  rw[vfmProgTheory.memory_cost_def]
QED

Theorem word_size_mono_leq:
  b1 ≤ b2 ⇒ word_size b1 ≤ word_size b2
Proof
  rw[word_size_def]
  \\ intLib.COOPER_TAC
QED

Theorem memory_cost_mono_leq:
  m1 ≤ m2 ⇒
  memory_cost m1 ≤ memory_cost m2
Proof
  rw[vfmExecutionTheory.memory_cost_def]
  \\ drule word_size_mono_leq
  \\ strip_tac
  \\ irule LESS_EQ_LESS_EQ_MONO
  \\ simp[]
  \\ irule DIV_LE_MONOTONE
  \\ simp[]
QED

(* TODO: general theorem *)
Theorem memory_cost_write_more_32_32:
  LENGTH l1 = 32
  ⇒
  memory_cost m1 0 32 +
  (memory_cost (l1 ++ (DROP 32 m1)) 32 32 + rest) =
  memory_cost m1 0 (32 + 32) + rest
Proof
  rw[memory_cost_def] \\ gvs[]
  \\ rw[memory_expansion_cost_def]
  \\ rw[word_size_def]
  \\ Cases_on`32 < LENGTH m1` \\ gvs[MAX_DEF]
  \\ rw[iffRL SUB_EQ_0] \\ gvs[]
  >- (
      `memory_cost 32 ≤ memory_cost 64` by simp[memory_cost_mono_leq]
   \\ `memory_cost (LENGTH m1) ≤ memory_cost 32` by simp[memory_cost_mono_leq]
   \\ intLib.COOPER_TAC)
  \\ `LENGTH m1 = 32` by simp[]
  \\ gvs[]
QED

Theorem memory_cost_write_more_64_32:
  LENGTH l1 = 64
  ⇒
  memory_cost m1 0 64 +
  (memory_cost (l1 ++ (DROP 64 m1)) 64 32 + rest) =
  memory_cost m1 0 (64 + 32) + rest
Proof
  rw[memory_cost_def] \\ gvs[]
  \\ rw[memory_expansion_cost_def]
  \\ rw[word_size_def]
  \\ Cases_on`64 < LENGTH m1` \\ gvs[MAX_DEF]
  \\ rw[iffRL SUB_EQ_0] \\ gvs[]
  >- (
      `memory_cost 64 ≤ memory_cost 96` by simp[memory_cost_mono_leq]
   \\ `memory_cost (LENGTH m1) ≤ memory_cost 64` by simp[memory_cost_mono_leq]
   \\ intLib.COOPER_TAC)
  \\ `LENGTH m1 = 64` by simp[]
  \\ gvs[]
QED

Theorem memory_cost_write_more_96_32:
  LENGTH l1 = 96
  ⇒
  memory_cost m1 0 96 +
  (memory_cost (l1 ++ (DROP 96 m1)) 96 32 + rest) =
  memory_cost m1 0 (96 + 32) + rest
Proof
  rw[memory_cost_def] \\ gvs[]
  \\ rw[memory_expansion_cost_def]
  \\ rw[word_size_def]
  \\ Cases_on`96 < LENGTH m1` \\ gvs[MAX_DEF]
  \\ rw[iffRL SUB_EQ_0] \\ gvs[]
  >- (
      `memory_cost 96 ≤ memory_cost 128` by simp[memory_cost_mono_leq]
   \\ `memory_cost (LENGTH m1) ≤ memory_cost 96` by simp[memory_cost_mono_leq]
   \\ intLib.COOPER_TAC)
  \\ `LENGTH m1 = 96` by simp[]
  \\ gvs[]
QED

Definition balance_slot_word_def:
  balance_slot_word (a:address) = (
      REVERSE (word_to_bytes (w2w a : bytes32) F) ++
      REVERSE (word_to_bytes (3w:bytes32) F))
End

Theorem LENGTH_balance_slot_word[simp]:
  LENGTH (balance_slot_word a) = 64
Proof
  rw[balance_slot_word_def]
QED

Theorem expanded_memory_leq:
  32 * word_size (a + b) ≤ LENGTH m ⇒ expanded_memory m a b = m
Proof
  rw[expanded_memory_def, memory_expand_by_def]
QED

Definition balance_slot_key_def:
  balance_slot_key (a:address) = word_of_bytes T (0w:bytes32) $
    Keccak_256_w64 (balance_slot_word a)
End

Definition Keccak_256_string_def:
  Keccak_256_string s =
  Keccak_256_w64 $ MAP (n2w o ORD) s
End

val () = cv_auto_trans Keccak_256_string_def;

Datatype:
  WETH_state = <|
    balances : address -> num
  ; allowances : address -> num
  ; locked : num
  ; touched : address set
  |>
End

Definition empty_WETH_state_def:
  empty_WETH_state = <|
    balances := K 0
  ; allowances := K 0
  ; locked := 0
  ; touched := {}
  |>
End

Definition total_balances_def:
  total_balances ws = SIGMA (ws.balances) ws.touched
End

Definition wf_WETH_state_def:
  wf_WETH_state ws ⇔
    { a | 0 < ws.balances a } SUBSET ws.touched ∧
    { a | 0 < ws.allowances a } SUBSET ws.touched ∧
    (∀a. ws.balances a < 2 ** 256) ∧
    (∀a. ws.allowances a < 2 ** 256) ∧
    ws.locked < 2 ** 256 ∧
    total_balances ws ≤ ws.locked
End

Theorem wf_empty_WETH_state[simp]:
  wf_WETH_state empty_WETH_state
Proof
  rw[wf_WETH_state_def, empty_WETH_state_def, total_balances_def,
     pred_setTheory.SUM_IMAGE_EMPTY]
QED

Definition WETH_deposit_def:
  WETH_deposit a n ws =
  ws with <|
    touched updated_by (INSERT) a
  ; balances updated_by (a =+ (n + ws.balances a))
  ; locked updated_by ((+) n)
  |>
End

Theorem wf_WETH_deposit:
  wf_WETH_state ws ∧
  ws.locked + n < 2 ** 256
  ⇒
  wf_WETH_state (WETH_deposit a n ws)
Proof
  qmatch_goalsub_abbrev_tac`_ < bnd`
  \\ rw[WETH_deposit_def, wf_WETH_state_def, APPLY_UPDATE_THM]
  \\ gvs[pred_setTheory.SUBSET_DEF] \\ rw[]
  \\ gvs[total_balances_def]
  >- (
    irule LESS_EQ_LESS_TRANS
    \\ goal_assum drule
    \\ simp[]
    \\ Cases_on`0 < ws.balances a` \\ simp[]
    \\ irule LESS_EQ_TRANS
    \\ goal_assum $ drule_at Any
    \\ irule pred_setTheory.SUM_IMAGE_IN_LE
    \\ simp[])
  \\ reverse $ Cases_on`a IN ws.touched`
  >- (
    gs[pred_setTheory.SUM_IMAGE_INSERT]
    \\ `~(0 < ws.balances a)` by metis_tac[]
    \\ gvs[]
    \\ qmatch_goalsub_abbrev_tac`s1 <= _`
    \\ qmatch_asmsub_abbrev_tac`s2 <= _`
    \\ `s1 = s2` suffices_by rw[]
    \\ simp[Abbr`s1`,Abbr`s2`]
    \\ irule pred_setTheory.SUM_IMAGE_CONG
    \\ rw[APPLY_UPDATE_THM]
    \\ gvs[] )
  \\ simp[iffLR pred_setTheory.ABSORPTION]
  \\ qpat_x_assum`_ <= _`mp_tac
  \\ drule_then (SUBST1_TAC o SYM) pred_setTheory.INSERT_DELETE
  \\ simp[pred_setTheory.SUM_IMAGE_INSERT]
  \\ qmatch_goalsub_abbrev_tac`s1 + _ <= _ ⇒ s2 + _ <= _`
  \\ `s1 = s2` suffices_by rw[]
  \\ simp[Abbr`s1`,Abbr`s2`]
  \\ irule pred_setTheory.SUM_IMAGE_CONG
  \\ rw[APPLY_UPDATE_THM]
QED

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
  ; blobVersionedHashes := []
  ; maxFeePerBlobGas := NONE
  ; maxFeePerGas := NONE
  ; authorizationList := []
  |>
End

val () = cv_auto_trans deploy_tx_def;

Definition deploy_block_def:
  deploy_block = <|
    baseFeePerGas := 0 (* fake *)
  ; excessBlobGas := 0 (* fake *)
  ; gasUsed := 7965074
  ; blobGasUsed := 0 (* fake *)
  ; number := 4719568
  ; timeStamp := 1513077455
  ; coinBase := 0x829BD824B016326A401d083B33D092293333A830w
  ; gasLimit := 7967026
  ; prevRandao := 0w (* fake *)
  ; hash := 0xd6e5f60d6b2367e74cd2aa520dbeb104826c3932eb482cc16e7f7ef5f8f74799w
  ; parentBeaconBlockRoot := 0w (* fake *)
  ; stateRoot := 0xb94a65da26a6c94c90376eb814d4f6f3c87d5b4ca515b1293b74a172be755245w
  ; transactions := [deploy_tx] (* not true, many others *)
  ; withdrawals := []
  ; requestsHash := 0w (* fake *)
  ; withdrawalsRoot := word_of_bytes T 0w (withdrawals_root [])
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
    case run_transaction (Collect empty_domain) F 1 []
           deploy_block deploy_accounts deploy_tx
    of SOME (res, ms) => SOME (res.result, ms) | _ => NONE
End

val () = cv_auto_trans deploy_tx_result_def;

Definition contract_code_def:
  contract_code = REVERSE $ hex_to_rev_bytes [] $
  "6060604052600436106100af576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806306fdde03146100b9578063095ea7b31461014757806318160ddd146101a157806323b872dd146101ca5780632e1a7d4d14610243578063313ce5671461026657806370a082311461029557806395d89b41146102e2578063a9059cbb14610370578063d0e30db0146103ca578063dd62ed3e146103d4575b6100b7610440565b005b34156100c457600080fd5b6100cc6104dd565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561010c5780820151818401526020810190506100f1565b50505050905090810190601f1680156101395780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561015257600080fd5b610187600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061057b565b604051808215151515815260200191505060405180910390f35b34156101ac57600080fd5b6101b461066d565b6040518082815260200191505060405180910390f35b34156101d557600080fd5b610229600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061068c565b604051808215151515815260200191505060405180910390f35b341561024e57600080fd5b61026460048080359060200190919050506109d9565b005b341561027157600080fd5b610279610b05565b604051808260ff1660ff16815260200191505060405180910390f35b34156102a057600080fd5b6102cc600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610b18565b6040518082815260200191505060405180910390f35b34156102ed57600080fd5b6102f5610b30565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561033557808201518184015260208101905061031a565b50505050905090810190601f1680156103625780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b341561037b57600080fd5b6103b0600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610bce565b604051808215151515815260200191505060405180910390f35b6103d2610440565b005b34156103df57600080fd5b61042a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610be3565b6040518082815260200191505060405180910390f35b34600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055503373ffffffffffffffffffffffffffffffffffffffff167fe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c346040518082815260200191505060405180910390a2565b60008054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156105735780601f1061054857610100808354040283529160200191610573565b820191906000526020600020905b81548152906001019060200180831161055657829003601f168201915b505050505081565b600081600460003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a36001905092915050565b60003073ffffffffffffffffffffffffffffffffffffffff1631905090565b600081600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101515156106dc57600080fd5b3373ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff16141580156107b457507fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205414155b156108cf5781600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015151561084457600080fd5b81600460008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055505b81600360008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600360008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190509392505050565b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410151515610a2757600080fd5b80600360003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055503373ffffffffffffffffffffffffffffffffffffffff166108fc829081150290604051600060405180830381858888f193505050501515610ab457600080fd5b3373ffffffffffffffffffffffffffffffffffffffff167f7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65826040518082815260200191505060405180910390a250565b600260009054906101000a900460ff1681565b60036020528060005260406000206000915090505481565b60018054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015610bc65780601f10610b9b57610100808354040283529160200191610bc6565b820191906000526020600020905b815481529060010190602001808311610ba957829003601f168201915b505050505081565b6000610bdb33848461068c565b905092915050565b60046020528160005260406000206020528060005260406000206000915091505054815600a165627a7a72305820deb4c2ccab3c2fdca32ab3f46728389c2fe2c165d5fafa07661e4e004f6c344a0029"
End

val () = cv_trans_deep_embedding EVAL contract_code_def;

Definition WETH_EVM_def:
  WETH_EVM addr ws a =
  let s = lookup_account addr a in
  wf_WETH_state ws ∧
  (∀a. balance_slot_key a ∉ {0w; 1w; 2w} ∧
       (a ∈ ws.touched ∨ balance_slot_key a ∉ IMAGE balance_slot_key ws.touched) ⇒
       lookup_storage (balance_slot_key a) s.storage = n2w (ws.balances a)) ∧
  (* TODO: same for allowances *)
  lookup_storage 0w s.storage =
    0x577261707065642045746865720000000000000000000000000000000000001Aw ∧
  lookup_storage 1w s.storage =
    0x5745544800000000000000000000000000000000000000000000000000000008w ∧
  lookup_storage 2w s.storage = 18w ∧
  s.balance = ws.locked ∧
  s.code = contract_code ∧
  s.nonce = 1
End

Theorem deploy_result_correct:
  ∃ms.
    deploy_tx_result = SOME (NONE, ms) ∧
    WETH_EVM 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2w empty_WETH_state ms
Proof
  CONV_TAC(STRIP_QUANT_CONV(PATH_CONV "lrlr" cv_eval))
  \\ qmatch_goalsub_abbrev_tac`SOME (_, ms)`
  \\ qexistsl_tac[`ms`]
  \\ conj_tac >- rw[]
  \\ rewrite_tac[WETH_EVM_def]
  \\ qmatch_goalsub_abbrev_tac`lookup_account addr ms`
  \\ simp[empty_WETH_state_def]
  \\ qmatch_asmsub_abbrev_tac`addr =+ s`
  \\ simp[Abbr`ms`, lookup_account_def, APPLY_UPDATE_THM]
  \\ simp[Abbr`addr`]
  \\ reverse conj_tac
  >- (
    qunabbrev_tac`s`
    \\ rewrite_tac[account_state_accessors]
    \\ conj_tac >- rw[lookup_storage_def, APPLY_UPDATE_THM]
    \\ conj_tac >- rw[lookup_storage_def, APPLY_UPDATE_THM]
    \\ conj_tac >- rw[lookup_storage_def, APPLY_UPDATE_THM]
    \\ CONV_TAC (RAND_CONV cv_eval)
    \\ CONV_TAC (listLib.list_EQ_CONV EVAL))
  \\ rw[Abbr`s`, lookup_storage_def, APPLY_UPDATE_THM]
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

fun evc tm = tm |> REWRITE_CONV[parsed_contract_code_eq]
                |> CONV_RULE (RAND_CONV EVAL)

val DROP_64_expanded_32_32 =
  cv_eval “32 * word_size (32 + 32) ≤ 64”
  |> EQT_ELIM
  |> MATCH_MP DROP_size_expanded_memory;

(* TODO: generalise? *)
Theorem DROP_64_expanded_memory_append_64_32:
  LENGTH l1 = 64 ⇒
  DROP 64 (expanded_memory (l1 ++ l2) 64 32) =
  expanded_memory l2 0 32
Proof
  rw[expanded_memory_def, DROP_APPEND,
     DROP_LENGTH_TOO_LONG, iffRL SUB_EQ_0]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[memory_expand_by_def, LEFT_ADD_DISTRIB, word_size_def]
  \\ rw[MAX_DEF]
QED

Theorem LENGTH_TAKE_64_expanded_memory_64_32[simp]:
  LENGTH (TAKE 64 (expanded_memory m 64 32)) = 64
Proof
  irule LENGTH_TAKE
  \\ irule LESS_EQ_TRANS
  \\ qexists_tac`32 * word_size (64 + 32)`
  \\ rw[LENGTH_expanded_memory_geq, MULT_32_word_size_96]
QED

Theorem Keccak256_gas_balance_slot_word_0_64:
  Keccak256_gas (balance_slot_word a ++ m) 0 64 = 42
Proof
  rw[Keccak256_gas_def]
  \\ CONV_TAC(PATH_CONV"lrlr"cv_eval)
  \\ simp[memory_cost_def]
  \\ simp[vfmExecutionTheory.memory_expansion_cost_def]
  \\ rw[word_size_def, MAX_DEF]
QED

Theorem mask_and_w2w:
  (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw:bytes32) &&
  w2w (w:address) = w2w w
Proof
  blastLib.BBLAST_TAC
QED

val word_of_bytes_tm = prim_mk_const{Thy="byte",Name="word_of_bytes"};
val word_to_bytes_tm = prim_mk_const{Thy="byte",Name="word_to_bytes"};

fun word_of_bytes_conv tm =
  let val (c,args) = strip_comb tm in
  if length args = 3 andalso
     same_const word_of_bytes_tm c andalso
     listSyntax.is_list (el 3 args)
  then cv_eval tm
  else raise UNCHANGED
  end

fun word_to_bytes_conv tm =
  let val (c,args) = strip_comb tm in
  if length args = 2 andalso
     same_const word_to_bytes_tm (fst (strip_comb tm))
  then cv_eval tm
  else raise UNCHANGED
  end

val no_data = ASSUME “(p:message_parameters).data = []”

Triviality conj_repeat:
  ((a ∧ a ∧ b) = (a ∧ b)) ∧
  ((a' ⇒ a) ⇒ ((a ∧ a' ∧ b) = (a' ∧ b)))
Proof
  rw[EQ_IMP_THM]
QED

Triviality conj_repeat_last:
  ((a' ⇒ a) ⇒ ((b ∧ a ∧ a') = (b ∧ a'))) ∧
  ((a' ⇒ a) ⇒ ((b ∧ a' ∧ a) = (b ∧ a')))
Proof
  rw[EQ_IMP_THM]
QED

local
  val SPEC_PushG = SPEC_Push |> Q.GENL[`n`,`bs`];
  val SPEC_DupG = SPEC_Dup |> Q.GEN`n`
  val SPEC_SwapG = SPEC_Swap |> Q.GEN`n`
  val SPEC_LogG = SPEC_Log |> Q.GEN`n`
in
  fun mk_SPEC_Push n bs = Q.SPECL[n,bs] SPEC_PushG
  fun mk_SPEC_Dup n = Q.SPEC n SPEC_DupG
  fun mk_SPEC_Swap n = Q.SPEC n SPEC_SwapG
  fun mk_SPEC_Log n = Q.SPEC n SPEC_LogG
end

val spec00 = SPEC_CallValue;
val spec01 = mk_SPEC_Push `1` `[3w]`;
val spec02 = mk_SPEC_Push `1` `[0w]`;
val spec03 = SPEC_Caller;
val spec04 = mk_SPEC_Push `20`
  `[255w; 255w; 255w; 255w; 255w; 255w; 255w; 255w; 255w; 255w;
    255w; 255w; 255w; 255w; 255w; 255w; 255w; 255w; 255w; 255w]`;
val spec05 = SPEC_And;
val spec06 = spec04;
val spec07 = spec05;
val spec08 = mk_SPEC_Dup `1`;
val spec09 = SPEC_MStore;
val spec10 = mk_SPEC_Push `1` `[32w]`;
val spec11 = SPEC_Add;
val spec12 = mk_SPEC_Swap `0`;
val spec13 = spec08;
val spec14 = spec09;
val spec15 = spec10;
val spec16 = spec11;
val spec17 = mk_SPEC_Push `1` `[0w]`;
val spec18 = SPEC_Keccak256;
val spec19 = spec17;
val spec20 = mk_SPEC_Dup `2`;
val spec21 = spec20;
val spec22 = SPEC_SLoad;
val spec23 = SPEC_Add;
val spec24 = mk_SPEC_Swap `2`;
val spec25 = SPEC_Pop;
val spec26 = SPEC_Pop;
val spec27 = spec08;
val spec28 = mk_SPEC_Swap `0`;
val spec29 = SPEC_SStore;
val spec30 = SPEC_Pop;
val spec31 = SPEC_Caller;
val spec32 = spec04;
val spec33 = SPEC_And;
val spec34 = mk_SPEC_Push `32`
  `[225w; 255w; 252w; 196w; 146w; 61w; 4w; 181w; 89w; 244w; 210w;
    154w; 139w; 252w; 108w; 218w; 4w; 235w; 91w; 13w; 60w; 70w; 7w;
    81w; 194w; 64w; 44w; 92w; 92w; 201w; 16w; 156w]`;
val spec35 = SPEC_CallValue;
val spec36 = mk_SPEC_Push `1` `[64w]`;
val spec37 = SPEC_MLoad;
val spec38 = mk_SPEC_Dup `0`;
val spec39 = mk_SPEC_Dup `2`;
val spec40 = mk_SPEC_Dup `1`;
val spec41 = SPEC_MStore;
val spec42 = mk_SPEC_Push `1` `[32w]`;
val spec43 = SPEC_Add;
val spec44 = mk_SPEC_Swap `1`;
val spec45 = SPEC_Pop;
val spec46 = SPEC_Pop;
val spec47 = mk_SPEC_Push `1` `[64w]`;
val spec48 = SPEC_MLoad;
val spec49 = mk_SPEC_Dup `0`;
val spec50 = mk_SPEC_Swap `1`;
val spec51 = SPEC_Sub;
val spec52 = mk_SPEC_Swap `0`;
val spec53 = mk_SPEC_Log `2`;
val spec54 = SPEC_Jump;

val th10 = SPEC_COMPOSE_RULE [
  spec00,spec01,spec02,spec03,spec04,spec05,spec06,spec07,spec08,spec09]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [opcode_def, SEP_CLAUSES, AC STAR_ASSOC STAR_COMM,
        AC CONJ_ASSOC CONJ_COMM, ADD1, mask_and_w2w, conj_repeat]
  |> CONV_RULE(DEPTH_CONV word_of_bytes_conv)
  |> SIMP_RULE (srw_ss() ++ ARITH_ss) [conj_repeat, mask_and_w2w];


val th10m =
  th10 |> SRULE [SPEC_MOVE_COND, STAR_ASSOC]
       |> Q.GENL[`offset`,`bytes`,`em`,`j`,`e`]
       |> SRULE[sumTheory.FORALL_SUM]
       |> SIMP_RULE (srw_ss() ++ ARITH_ss) [GSYM SPEC_MOVE_COND, conj_repeat]

val evm_domain_ty = “:evm_el set set”;
fun extract_conds th = let
  val pre = th |> concl |> dest_spec |> #2
  val pres = list_dest dest_star pre
  val front = butlast pres
  val (cond, conj) = dest_comb $ last pres
  fun replace conds = let
    val cond = mk_comb(cond, list_mk_conj conds)
  in list_mk_star (front @ [cond]) evm_domain_ty end
in
  (strip_conj conj, replace)
end

val (conds, replace) = extract_conds th10m
val (th10wi, gl) = SPEC_STRENGTHEN_RULE th10m $ replace $
   “96 ≤ LENGTH (m:byte list)” ::
   “TAKE 32 (DROP 64 m) = REVERSE (word_to_bytes (96w:bytes32) F)” ::
   conds

Theorem gl[local]:
  ^gl
Proof
  srw_tac[star_ss][SEP_IMP_def]
  \\ gvs[STAR_def, PULL_EXISTS]
  \\ gvs[cond_def]
  \\ first_x_assum $ irule_at (Pos(el 2))
  \\ first_x_assum $ irule_at (Pos(el 3))
  \\ first_x_assum $ irule_at (Pos(el 4))
  \\ first_x_assum $ irule_at (Pos(el 5))
  \\ first_x_assum $ irule_at (Pos(el 6))
  \\ first_x_assum $ irule_at (Pos(el 7))
  \\ first_x_assum $ irule_at (Pos(el 8))
  \\ metis_tac[]
QED

val th10w = MP th10wi gl

val th10x = th10w
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
     [SPEC_MOVE_COND, MULT_32_word_size_32,
      memory_cost_none_zero,
      expanded_memory_leq, AC CONJ_ASSOC CONJ_COMM]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [GSYM AND_IMP_INTRO, memory_cost_none_zero, MULT_32_word_size_32]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [AND_IMP_INTRO, GSYM SPEC_MOVE_COND,
        AC CONJ_ASSOC CONJ_COMM, conj_repeat]

(* --- *)

(*
val th = spec14
*)

fun prepare prefix th = let
  val th1 = th |> REWRITE_RULE [SPEC_MOVE_COND] |> UNDISCH_ALL
  val (_,pre,_,post) = th1 |> concl |> dest_spec
  fun add_prime v = variant [v] v (* TODO improve? *)
  val part_names = list_dest dest_star pre
                     |> map (fn tm => dest_comb tm)
  val parts = list_dest dest_star post
  (*
  val p = hd parts
  *)
  fun update_one p = let
    val (a,e) = dest_comb p
    val v = snd (first (aconv a o fst) part_names)
    in if aconv e v then (p,[]) else let
      val v' = add_prime v
      val new_eq = mk_eq(v',e)
      in (mk_comb(a,v'), [new_eq]) end
    end
  fun update_all [] = ([],[])
    | update_all (p::ps) = let
        val (p,aux1) = update_one p
        val (ps,aux2) = update_all ps
        in (p::ps, aux1 @ aux2) end
  val (ps,aux) = update_all parts
  val new_post = list_mk_star ps evm_domain_ty
  val new_assums = list_mk_conj aux
  val goal = mk_imp(new_assums, mk_eq(post,new_post))
  val lemma = prove(goal,rpt strip_tac \\ asm_rewrite_tac [])
  fun D th = if is_imp (concl th) then th else DISCH T th
  val th2 = th1 |> CONV_RULE (RAND_CONV (REWR_CONV (UNDISCH lemma)))
  val th3 = th2 |> DISCH new_assums |> DISCH_ALL
                |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  val vs = free_vars (concl th3)
  (* val prefix = "_0_" *)
  fun add_prefix prefix v = mk_var(prefix ^ fst (dest_var v), type_of v)
  val s = map (fn v => v |-> add_prefix prefix v) vs
  val th4 = INST s th3
  in UNDISCH_ALL th4 end

fun prepare_list thms = let
  val xs = mapi (fn i => fn th => ("v" ^ Int.toString i ^ "_", (th:thm))) thms
  in map (fn (prefix,th) => prepare prefix th) xs end

val res =
  [spec10,spec11,spec12,spec13,spec14,spec15,spec16,spec17]
  |> prepare_list |> SPEC_COMPOSE_RULE;

(* --- *)

val th18 = SPEC_COMPOSE_RULE [th10x,
  spec10,spec11,spec12,spec13,spec14,spec15,spec16,spec17]
  |> CONV_RULE(DEPTH_CONV word_of_bytes_conv)
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [opcode_def, SEP_CLAUSES, AC STAR_ASSOC STAR_COMM,
        AC CONJ_ASSOC CONJ_COMM, conj_repeat, ADD1]
  |> CONV_RULE(DEPTH_CONV word_of_bytes_conv)
  |> SIMP_RULE (srw_ss() ++ ARITH_ss) [
       conj_repeat_last, DROP_64_expanded_32_32]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss) [
      cv_eval “32 * word_size (0 + 32) ≤ 32”
      |> EQT_ELIM
      |> MATCH_MP DROP_size_expanded_memory];

val th18m =
  th18 |> SRULE [SPEC_MOVE_COND, STAR_ASSOC]
       |> Q.GENL[`offset`,`bytes`,`em`]
       |> SRULE[GSYM SPEC_MOVE_COND]
       |> SIMP_RULE (srw_ss() ++ ARITH_ss)
            [TAKE_APPEND1, LENGTH_word_to_bytes,
             TAKE_LENGTH_TOO_LONG, DROP_APPEND, DROP_DROP_T,
             DROP_LENGTH_TOO_LONG, DROP_64_expanded_32_32]

val th22 = SPEC_COMPOSE_RULE [th18m,spec18,spec19,spec20,spec21]
  |> CONV_RULE(DEPTH_CONV word_of_bytes_conv)
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [opcode_def, SEP_CLAUSES, AC STAR_ASSOC STAR_COMM,
        AC CONJ_ASSOC CONJ_COMM, conj_repeat, ADD1]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [conj_repeat_last, TAKE_APPEND1,
        TAKE_LENGTH_TOO_LONG,
        DROP_LENGTH_TOO_LONG, DROP_APPEND, DROP_DROP_T,
        LENGTH_word_to_bytes, DROP_64_expanded_32_32];

val th22m =
  th22 |> SRULE [SPEC_MOVE_COND, STAR_ASSOC]
       |> Q.GENL[`offset`,`em`,`sz`]
       |> SRULE [GSYM SPEC_MOVE_COND];

val th29 = SPEC_COMPOSE_RULE
  [th22m, spec22, spec23, spec24, spec25, spec26, spec27, spec28]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [opcode_def, ADD1, SEP_CLAUSES, AC STAR_ASSOC STAR_COMM,
        AC CONJ_ASSOC CONJ_COMM, conj_repeat]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [conj_repeat_last, TAKE_LENGTH_TOO_LONG, TAKE_APPEND1,
        LENGTH_word_to_bytes];

val th29m =
  th29 |> SRULE [SPEC_MOVE_COND, STAR_ASSOC,
                 GSYM balance_slot_word_def, GSYM balance_slot_key_def]
       |> Q.GENL[`key`,`sk`]
       |> SIMP_RULE (srw_ss() ++ ARITH_ss)
            [GSYM SPEC_MOVE_COND,expanded_memory_leq,MULT_32_word_size_64];


val th38 = SPEC_COMPOSE_RULE
           [th29m, spec29, spec30, spec31, spec32,
            spec33, spec34, spec35, spec36, spec37]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [opcode_def, ADD1, SEP_CLAUSES, AC STAR_ASSOC STAR_COMM,
        AC CONJ_ASSOC CONJ_COMM, conj_repeat]
  |> CONV_RULE(DEPTH_CONV word_of_bytes_conv)
  |> SIMP_RULE (srw_ss() ++ ARITH_ss) [mask_and_w2w];

val th38m =
  th38 |> SRULE [SPEC_MOVE_COND, STAR_ASSOC]
  |> Q.GENL[`value`,`em`,`sk`,`key`,`offset`]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [expanded_memory_leq,
        LENGTH_word_to_bytes,
        DROP_64_expanded_memory_append_64_32,
        Keccak256_gas_balance_slot_word_0_64,
        memory_cost_write_more_64_32,
        MULT_32_word_size_96,
        MULT_32_word_size_64,
        memory_cost_none_zero,
        memory_cost_write_more_32_32, GSYM AND_IMP_INTRO]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [GSYM SPEC_MOVE_COND, conj_repeat_last,
        AND_IMP_INTRO, AC CONJ_ASSOC CONJ_COMM]

val th48 = SPEC_COMPOSE_RULE
           [th38m, spec38, spec39, spec40, spec41, spec42,
            spec43, spec44, spec45, spec46, spec47]
    |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [opcode_def, ADD1, SEP_CLAUSES, AC STAR_ASSOC STAR_COMM,
        AC CONJ_ASSOC CONJ_COMM, conj_repeat]

val th48m =
  th48 |> SRULE [SPEC_MOVE_COND, STAR_ASSOC]
  |> Q.GENL[`bytes`,`em`,`offset`]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [TAKE_expanded_memory_leq,
        TAKE_APPEND2, TAKE_LENGTH_TOO_LONG]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [GSYM SPEC_MOVE_COND, conj_repeat_last]
  |> CONV_RULE (DEPTH_CONV word_of_bytes_conv)
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [expanded_memory_leq, DROP_size_expanded_memory,
        MULT_32_word_size_128,
        DROP_APPEND, DROP_DROP_T, DROP_LENGTH_TOO_LONG]

val th53 =
  SPEC_COMPOSE_RULE[th48m, spec48, spec49, spec50, spec51, spec52]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
     [opcode_def, ADD1, SEP_CLAUSES, AC STAR_ASSOC STAR_COMM,
      AC CONJ_ASSOC CONJ_COMM, conj_repeat]

val th53m =
  th53 |> SRULE [SPEC_MOVE_COND, STAR_ASSOC]
  |> Q.GENL[`em`,`offset`]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [expanded_memory_leq, LENGTH_word_to_bytes,
        DROP_size_expanded_memory, MULT_32_word_size_96,
        DROP_APPEND, DROP_LENGTH_TOO_LONG,
        TAKE_APPEND1, TAKE_REVERSE, LASTN_DROP,
        memory_cost_none_zero]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [GSYM SPEC_MOVE_COND, conj_repeat_last]

val th55 =
  SPEC_COMPOSE_RULE[th53m, spec53, spec54]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [opcode_def, ADD1, SEP_CLAUSES, AC STAR_ASSOC STAR_COMM,
        AC CONJ_ASSOC CONJ_COMM, conj_repeat]

val th55m =
  th55 |> SRULE [SPEC_MOVE_COND, STAR_ASSOC]
  |> Q.GENL[`em`,`offset`,`sz`,`dynamicGas`,`ev`]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [expanded_memory_leq, LENGTH_word_to_bytes,
        DROP_size_expanded_memory, MULT_32_word_size_96,
        MULT_32_word_size_128,
        DROP_APPEND, DROP_LENGTH_TOO_LONG, TAKE_APPEND1, TAKE_REVERSE,
        LASTN_DROP, memory_cost_none_zero,
        NOT_LENGTH_ADD_LEQ, log_data_cost_def, log_topic_cost_def]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [GSYM SPEC_MOVE_COND, conj_repeat_last]

Theorem SPEC_deposit = th55m;

val s0 = mk_SPEC_Push `1` `[96w]`
val s1 = mk_SPEC_Push `1` `[64w]`
val s2 = SPEC_MStore
val s3 = mk_SPEC_Push `1` `[4w]`
val s4 = SPEC_CallDataSize
val s5 = SPEC_LT
val s6 = mk_SPEC_Push `2` `[0w; 175w]`
val s7 = SPEC_JumpI_take
val s8 = SPEC_JumpDest
val s9 = mk_SPEC_Push `2` `[0w; 183w]`
val s10 = mk_SPEC_Push `2` `[4w; 64w]`
val s11 = SPEC_Jump

val startup =
  SPEC_COMPOSE_RULE [s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
     [opcode_def, ADD1, SEP_CLAUSES, AC STAR_ASSOC STAR_COMM,
      AC CONJ_ASSOC CONJ_COMM, conj_repeat]

val sm =
  startup |> SRULE [SPEC_MOVE_COND, STAR_ASSOC]
  |> Q.GENL[`em`,`offset`,`bytes`]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss) [GSYM SPEC_MOVE_COND]
  |> CONV_RULE (DEPTH_CONV word_of_bytes_conv)
  |> SIMP_RULE (srw_ss() ++ ARITH_ss) []

val p = “p:message_parameters”
fun has_term p = can (find_term (can (match_term p)))

val (conds, replace) = extract_conds sm
val (smi, gl) = SPEC_STRENGTHEN_RULE sm $ replace $
   “p.parsed = parsed_contract_code” ::
   “p.code = contract_code” ::
   “LENGTH p.data < 4” ::
   List.filter (fn tm =>
     not (has_term “^p.code” tm orelse
          has_term “^p.parsed” tm orelse
          has_term “^p.data” tm orelse
          has_term “g + 6n” tm )) conds

Theorem gl[local]:
  ^gl
Proof
  rw[SEP_IMP_def, STAR_def, PULL_EXISTS, cond_def]
  \\ goal_assum irule
  \\ conj_tac >- CONV_TAC cv_eval
  \\ conj_tac >- CONV_TAC cv_eval
  \\ conj_tac >- CONV_TAC evc
  \\ conj_tac >- CONV_TAC evc
  \\ rpt $ goal_assum $ drule
QED

val smw = MP smi gl
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
       [AC CONJ_ASSOC CONJ_COMM, conj_repeat]
  |> Q.INST[`e` |-> `INL ()`]

(* TODO: simplify by assuming m starts as []? *)

Theorem SPEC_fallback_code[local] =
  SPEC_COMPOSE_RULE [smw, SPEC_JumpDest, th55m]
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
     [opcode_def, ADD1, SEP_CLAUSES, AC STAR_ASSOC STAR_COMM,
      AC CONJ_ASSOC CONJ_COMM, conj_repeat]
  |> SRULE [SPEC_MOVE_COND, STAR_ASSOC]
  |> Q.GENL [`pc`,`j`,`orig_rb`]
  |> Q.SPEC`0`
  |> SIMP_RULE (srw_ss() ++ ARITH_ss)
     [LENGTH_TAKE, LENGTH_expanded_memory_geq, iffRL SUB_EQ_0,
      MULT_32_word_size_96, DROP_APPEND, DROP_LENGTH_TOO_LONG,
      TAKE_APPEND1, LENGTH_word_to_bytes,DROP_DROP_T,
      DROP_size_expanded_memory, MULT_32_word_size_128,
      Q.SPECL[`64`,`32`](Q.GENL[`off`,`sz`]memory_cost_offset_to_0),
      memory_cost_write_more_96_32]
  |> SRULE[GSYM AND_IMP_INTRO, evc“FLOOKUP parsed_contract_code 183”,
           cv_eval“LENGTH contract_code”]
  |> SRULE[AND_IMP_INTRO, GSYM SPEC_MOVE_COND, AC CONJ_ASSOC CONJ_COMM]

val code_req = SPEC_fallback_code |> concl |> strip_comb |> #2 |> el 3;

Theorem code_req_met[local]:
  ∀n i. (n,i) ∈ ^code_req ⇒ FLOOKUP parsed_contract_code n = SOME i
Proof
  rpt gen_tac
  \\ rewrite_tac[pred_setTheory.IN_INSERT, pairTheory.PAIR_EQ]
  \\ reverse strip_tac
  >- gvs[]
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ CONV_TAC evc
QED

Definition fmap_entries_def:
  fmap_entries fm = {(k,v) | FLOOKUP fm k = SOME v}
End

val SPEC_fallback_code_lemma =
  MATCH_MP SPEC_SUBSET_CODE SPEC_fallback_code
  |> Q.SPEC ‘fmap_entries parsed_contract_code’

Theorem SPEC_fallback_code_cond[local]:
  ^(SPEC_fallback_code_lemma |> concl |> dest_imp |> fst)
Proof
  rewrite_tac [pred_setTheory.SUBSET_DEF]
  \\ Cases \\ strip_tac
  \\ simp[fmap_entries_def]
  \\ drule_then ACCEPT_TAC code_req_met
QED

Theorem FST_SND_SND_EVM_MODEL[local]:
  FST(SND(SND EVM_MODEL)) = EVM_INSTR
Proof
  rw[EVM_MODEL_def]
QED

Theorem SPEC_fallback =
  MP SPEC_fallback_code_lemma SPEC_fallback_code_cond
  |> ONCE_REWRITE_RULE[GSYM SPEC_CODE]
  |> REWRITE_RULE[FST_SND_SND_EVM_MODEL]

(*
evc “FLOOKUP parsed_contract_code 0”
evc “FLOOKUP parsed_contract_code 2”
evc “FLOOKUP parsed_contract_code 4”
evc “FLOOKUP parsed_contract_code 5”
evc “FLOOKUP parsed_contract_code 7”
evc “FLOOKUP parsed_contract_code 8”
evc “FLOOKUP parsed_contract_code 9”
evc “FLOOKUP parsed_contract_code 12”
evc “FLOOKUP parsed_contract_code 175”
evc “FLOOKUP parsed_contract_code 176”
evc “FLOOKUP parsed_contract_code 179”
evc “FLOOKUP parsed_contract_code 182”
evc “FLOOKUP parsed_contract_code 1088”
evc “FLOOKUP parsed_contract_code 1089”
evc “FLOOKUP parsed_contract_code 1090”
evc “FLOOKUP parsed_contract_code 1092”
evc “FLOOKUP parsed_contract_code 1094”
evc “FLOOKUP parsed_contract_code 1095”
evc “FLOOKUP parsed_contract_code 1116”
evc “FLOOKUP parsed_contract_code 1138”
evc “FLOOKUP parsed_contract_code 1139”
evc “FLOOKUP parsed_contract_code 1140”
evc “FLOOKUP parsed_contract_code 1141”
evc “FLOOKUP parsed_contract_code 1143”
evc “FLOOKUP parsed_contract_code 1144”
evc “FLOOKUP parsed_contract_code 1145”
evc “FLOOKUP parsed_contract_code 1146”
evc “FLOOKUP parsed_contract_code 1147”
evc “FLOOKUP parsed_contract_code 1149”
evc “FLOOKUP parsed_contract_code 1150”
evc “FLOOKUP parsed_contract_code 1152”
evc “FLOOKUP parsed_contract_code 1153”
evc “FLOOKUP parsed_contract_code 1155”
evc “FLOOKUP parsed_contract_code 1156”
evc “FLOOKUP parsed_contract_code 1157”
evc “FLOOKUP parsed_contract_code 1158”
evc “FLOOKUP parsed_contract_code 1159”
evc “FLOOKUP parsed_contract_code 1160”
evc “FLOOKUP parsed_contract_code 1161”
evc “FLOOKUP parsed_contract_code 1162”
evc “FLOOKUP parsed_contract_code 1163”
evc “FLOOKUP parsed_contract_code 1164”
evc “FLOOKUP parsed_contract_code 1165”
evc “FLOOKUP parsed_contract_code 1166”
evc “FLOOKUP parsed_contract_code 1167”
evc “FLOOKUP parsed_contract_code 1188”
evc “FLOOKUP parsed_contract_code 1189”
evc “FLOOKUP parsed_contract_code 1222”
evc “FLOOKUP parsed_contract_code 1223”
evc “FLOOKUP parsed_contract_code 1225”
evc “FLOOKUP parsed_contract_code 1226”
evc “FLOOKUP parsed_contract_code 1227”
evc “FLOOKUP parsed_contract_code 1228”
evc “FLOOKUP parsed_contract_code 1229”
evc “FLOOKUP parsed_contract_code 1230”
evc “FLOOKUP parsed_contract_code 1232”
evc “FLOOKUP parsed_contract_code 1233”
evc “FLOOKUP parsed_contract_code 1234”
evc “FLOOKUP parsed_contract_code 1235”
evc “FLOOKUP parsed_contract_code 1236”
evc “FLOOKUP parsed_contract_code 1238”
evc “FLOOKUP parsed_contract_code 1239”
evc “FLOOKUP parsed_contract_code 1240”
evc “FLOOKUP parsed_contract_code 1241”
evc “FLOOKUP parsed_contract_code 1242”
evc “FLOOKUP parsed_contract_code 1243”
evc “FLOOKUP parsed_contract_code 1244”
evc “FLOOKUP parsed_contract_code 183”
evc “FLOOKUP parsed_contract_code 184”
*)

(*
Theorem call_follows_abi_4bytes:
  tx.to = SOME addr ∧
  (lookup_account addr ms).code = contract_code ∧
  run_transaction F 1 ph bk ms tx = SOME (res, ms2) ∧
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
