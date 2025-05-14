open HolKernel boolLib bossLib Parse vfmTypesTheory

val () = new_theory "vfmConstants";

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

Definition min_base_fee_per_blob_gas_def:
  min_base_fee_per_blob_gas = 1n
End

Definition blob_base_fee_update_fraction_def:
  blob_base_fee_update_fraction = 3338477n
End

Definition max_blob_gas_per_block_def:
  max_blob_gas_per_block = 786432n
End

Definition target_blob_gas_per_block_def:
  target_blob_gas_per_block = 393216n
End

Definition versioned_hash_version_kzg_def:
  versioned_hash_version_kzg: byte = 1w
End

val () = export_theory();
