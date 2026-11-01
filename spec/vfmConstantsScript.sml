Theory vfmConstants
Ancestors vfmTypes

Definition stack_limit_def[simp]:
  stack_limit = 1024n
End

Definition context_limit_def[simp]:
  context_limit = 1024n
End

(* EIP-2780: one ECDSA recovery, the sender's access and write, and the
   transaction's bytes in the block.  What the transaction reaches adds to
   it, in `tx_intrinsic_base`. *)
Definition base_cost_def:
  base_cost = 12000n
End

(* EIP-8038: ACCOUNT_WRITE + COLD_ACCOUNT_ACCESS.  EIP-2780 charges it as the
   intrinsic cost of a create transaction, and EIP-8038 charges it as the
   CREATE/CREATE2 opcode's own cost (`static_gas`), where it replaces EIP-170's
   flat 32000. *)
Definition create_cost_def:
  create_cost = 12000n
End

(* EIP-7825: the execution gas a transaction may be granted.  EIP-8037
   bounds the intrinsic and the calldata floor by it separately, and caps
   the two dimensions' sum by `tx_max_total_gas_limit`. *)
Definition tx_max_gas_limit_def[simp]:
  tx_max_gas_limit = 2n ** 24
End

Definition tx_max_total_gas_limit_def[simp]:
  tx_max_total_gas_limit = 2n ** 32 - 1
End

(* EIP-2780: sending value to an account other than the sender's own. *)
Definition tx_value_cost_def:
  tx_value_cost = 6000n
End

Definition call_data_cost_def:
  call_data_cost is_zero =
  if is_zero then 4n else 16
End

(* EIP-7976: every calldata byte counts as four tokens, so the floor is
   64 gas a byte. *)
Definition floor_call_data_cost_def:
  floor_call_data_cost = 16n
End

Definition init_code_word_cost_def:
  init_code_word_cost = 2n
End

(* EIP-7954 *)
Definition max_code_size_def:
  max_code_size = 0x10000n
End

Definition warm_access_cost_def:
  warm_access_cost = 100n
End

Definition cold_sload_cost_def:
  cold_sload_cost = 2100n
End

Definition cold_access_cost_def:
  cold_access_cost = 3000n
End

Definition memory_cost_per_word_def:
  memory_cost_per_word = 3n
End

Definition memory_copy_cost_def:
  memory_copy_cost = 3n
End

Definition exp_per_byte_cost_def:
  exp_per_byte_cost = 50n
End

(* A keccak word, which is what a code deposit costs in execution gas: EIP-170's
   200 a byte is gone, and the bytes are EIP-8037 state gas instead. *)
Definition keccak256_per_word_cost_def:
  keccak256_per_word_cost = 6n
End

(* EIP-8038: STORAGE_SET and COLD_STORAGE_WRITE collapse into one
   STORAGE_WRITE, charged each time a slot moves away from its
   transaction-start value and refunded when it is restored. *)
Definition storage_write_cost_def:
  storage_write_cost = 10000n
End

(* EIP-8038: (STORAGE_WRITE + COLD_STORAGE_ACCESS) * 4800 / 5000. *)
Definition storage_clear_refund_def:
  storage_clear_refund = 11616n
End

(* EIP-8037: the state gas a first-time set of a zero slot pays for, 64
   state bytes at COST_PER_STATE_BYTE, and what a slot set then cleared
   credits back.  State gas, not execution gas: it draws on the frame's
   reservoir (vfmContext's `stateGasLeft`) before execution gas. *)
Definition cost_per_state_byte_def:
  cost_per_state_byte = 1530n
End

Definition state_bytes_per_storage_set_def:
  state_bytes_per_storage_set = 64n
End

Definition storage_set_state_gas_def:
  storage_set_state_gas =
    state_bytes_per_storage_set * cost_per_state_byte
End

Definition state_bytes_per_new_account_def:
  state_bytes_per_new_account = 120n
End

(* EIP-8037: a new account's creation, 120 state bytes at COST_PER_STATE_BYTE.
   EIP-8038 drops the 25000 execution gas it used to carry. *)
Definition new_account_state_gas_def:
  new_account_state_gas =
    state_bytes_per_new_account * cost_per_state_byte
End

(* EIP-8037: the 23 state bytes a net-new delegation indicator costs, charged
   at the top frame when EIP-7702's authorizations run. *)
Definition state_bytes_per_auth_base_def:
  state_bytes_per_auth_base = 23n
End

Definition auth_base_state_gas_def:
  auth_base_state_gas =
    state_bytes_per_auth_base * cost_per_state_byte
End

Definition log_topic_cost_def:
  log_topic_cost = 375n
End

Definition log_data_cost_def:
  log_data_cost = 8n
End

(* EIP-8037: the state-independent part of what one authorization costs, which
   EIP-2780 charges in the intrinsic.  The state-dependent part (the new
   account, the first write, the delegation bytes) is charged at the top
   frame, so an existing authority has nothing to refund any more. *)
Definition execution_per_auth_base_cost_def:
  execution_per_auth_base_cost = 7816n
End

(* EIP-8038: ACCOUNT_WRITE + CALL_STIPEND *)
Definition call_value_cost_def:
  call_value_cost = 11300n
End

(* EIP-8038: ACCOUNT_WRITE, the execution-gas charge for the first write to
   an account leaf.  A sweep that creates its beneficiary pays it, and so does
   each EIP-7702 authorization that writes its authority's leaf; the state gas
   a creation also carries is EIP-8037's and charged separately. *)
Definition account_write_cost_def:
  account_write_cost = 9000n
End

Definition call_stipend_def:
  call_stipend = 2300n
End

Definition word_size_def:
  word_size byteSize = (byteSize + 31) DIV 32
End

(* EIP-8038: COLD_ACCOUNT_ACCESS - WARM_ACCESS, and
   COLD_STORAGE_ACCESS - WARM_ACCESS. *)
Definition access_list_address_cost_def:
  access_list_address_cost = 2900n
End

Definition access_list_storage_key_cost_def:
  access_list_storage_key_cost = 2000n
End

(* EIP-7981: an access list entry's own data is charged at the calldata
   floor's token price as well as its per-entry cost, as 80 tokens for an
   address and 128 for a storage key: 1280 and 2048 gas. *)
Definition access_list_address_floor_tokens_def:
  access_list_address_floor_tokens = 80n
End

Definition access_list_storage_key_floor_tokens_def:
  access_list_storage_key_floor_tokens = 128n
End

Definition gas_per_blob_def:
  gas_per_blob = 2n ** 17
End

Definition blob_base_cost_def:
  blob_base_cost = 2n ** 13
End

Definition min_base_fee_per_blob_gas_def:
  min_base_fee_per_blob_gas = 1n
End

(* Amsterdam is built on the bpo lineage rather than the Osaka one, so it
   carries BPO2's blob schedule: 14 target blobs and 21 maximum, with its
   own base fee update fraction.  This is not one of Amsterdam's EIPs,
   but the forks it is scheduled from bring it along. *)
Definition blob_base_fee_update_fraction_def:
  blob_base_fee_update_fraction = 11684671n
End

Definition max_blob_gas_per_block_def:
  max_blob_gas_per_block = 2752512n
End

Definition target_blob_gas_per_block_def:
  target_blob_gas_per_block = 1835008n
End

Definition max_blobs_per_tx_def:
  max_blobs_per_tx = 6n
End

Definition versioned_hash_version_kzg_def:
  versioned_hash_version_kzg: byte = 1w
End

Definition deposit_contract_address_def:
  deposit_contract_address : address =
    0x00000000219ab540356cBB839Cbe05303d7705Faw
End

Definition deposit_event_topic_def:
  deposit_event_topic : bytes32 =
    0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5w
End

(* EIP-7708: the system address logs every ETH transfer. *)
Definition system_address_def:
  system_address : address =
    0xfffffffffffffffffffffffffffffffffffffffew
End

Definition transfer_topic_def:
  transfer_topic : bytes32 =
    0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3efw
End

(* EIP-7708: the log a transfer of `amount` from `sender` to `recipient`
   emits, if it emits one at all.  A transfer to self moves nothing, and
   a zero transfer is not a transfer. *)
Definition transfer_log_def:
  transfer_log (sender: address) (recipient: address) (amount: num) : event list =
    if amount = 0 ∨ sender = recipient then [] else
      [<| logger := system_address
        ; topics := [transfer_topic; w2w sender; w2w recipient]
        ; data := word_to_bytes (n2w amount : bytes32) T |>]
End

Definition withdrawal_request_contract_def:
  withdrawal_request_contract : address =
    0x00000961Ef480Eb55e80D19ad83579A64c007002w
End

Definition consolidation_request_contract_def:
  consolidation_request_contract : address =
    0x0000BBdDc7CE488642fb579F8B00f3a590007251w
End

Definition max_withdrawal_requests_per_block_def:
  max_withdrawal_requests_per_block = 16n
End

Definition target_withdrawal_requests_per_block_def:
  target_withdrawal_requests_per_block = 2n
End

Definition max_consolidation_requests_per_block_def:
  max_consolidation_requests_per_block = 2n
End

Definition target_consolidation_requests_per_block_def:
  target_consolidation_requests_per_block = 1n
End

Definition min_gas_limit_def:
  min_gas_limit = 5000n
End

Definition gas_limit_adjustment_factor_def:
  gas_limit_adjustment_factor = 1024n
End

Definition base_fee_max_change_denominator_def:
  base_fee_max_change_denominator = 8n
End

Definition elasticity_multiplier_def:
  elasticity_multiplier = 2n
End

(* EIP-7934: MAX_BLOCK_SIZE (10 MiB) - SAFETY_MARGIN (2 MiB) *)
Definition max_rlp_block_size_def:
  max_rlp_block_size = 8388608n
End
