Theory vfmConstants
Ancestors vfmTypes

Definition stack_limit_def[simp]:
  stack_limit = 1024n
End

Definition context_limit_def[simp]:
  context_limit = 1024n
End

Definition base_cost_def:
  base_cost = 21000n
End

Definition create_cost_def:
  create_cost = 32000n
End

Definition call_data_cost_def:
  call_data_cost is_zero =
  if is_zero then 4n else 16
End

Definition floor_call_data_cost_def:
  floor_call_data_cost = 10n
End

Definition init_code_word_cost_def:
  init_code_word_cost = 2n
End

Definition max_code_size_def:
  max_code_size = 0x6000n
End

Definition code_deposit_cost_def:
  code_deposit_cost = 200n
End

Definition warm_access_cost_def:
  warm_access_cost = 100n
End

Definition cold_sload_cost_def:
  cold_sload_cost = 2100n
End

Definition cold_access_cost_def:
  cold_access_cost = 2600n
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

Definition keccak256_per_word_cost_def:
  keccak256_per_word_cost = 6n
End

Definition storage_set_cost_def:
  storage_set_cost = 20000n
End

Definition storage_update_cost_def:
  storage_update_cost = 5000n
End

Definition storage_clear_refund_def:
  storage_clear_refund = 4800n
End

Definition log_topic_cost_def:
  log_topic_cost = 375n
End

Definition log_data_cost_def:
  log_data_cost = 8n
End

Definition new_account_cost_def:
  new_account_cost = 25000n
End

Definition call_value_cost_def:
  call_value_cost = 9000n
End

Definition self_destruct_new_account_cost_def:
  self_destruct_new_account_cost = 25000n
End

Definition call_stipend_def:
  call_stipend = 2300n
End

Definition word_size_def:
  word_size byteSize = (byteSize + 31) DIV 32
End

Definition access_list_address_cost_def:
  access_list_address_cost = 2400n
End

Definition access_list_storage_key_cost_def:
  access_list_storage_key_cost = 1900n
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

Definition blob_base_fee_update_fraction_def:
  blob_base_fee_update_fraction = 5007716n
End

Definition max_blob_gas_per_block_def:
  max_blob_gas_per_block = 1179648n
End

Definition target_blob_gas_per_block_def:
  target_blob_gas_per_block = 786432n
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

Definition base_fee_max_change_denominator_def:
  base_fee_max_change_denominator = 8n
End

Definition elasticity_multiplier_def:
  elasticity_multiplier = 2n
End
