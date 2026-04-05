# Verifereum Cleanup Items

Generated 2026-04-04 from code review.

## 🟡 Medium Priority

### Move ~300 lines of pure spec decompositions out of `vfmProgScript.sml`

Lines ~957–1270 contain definitions and theorems that decompose the monadic
EVM spec into pure functional forms. They don't depend on the program logic
framework (`evm2set`, `SPEC`, `SEP_EQ`, etc.) and could move to
`vfmExecutionPropScript.sml` or a new sibling theory. Categories:

1. **Access/domain operation splits**: `msdomain_add_def`, `accesses_add_def`,
   `access_cost_def`, `access_check_def`, `access_address_split`,
   `msdomain_add_slot_def`, `accesses_add_slot_def`, `access_slot_cost_def`,
   `access_slot_check_def`, `access_slot_split`, `access_storage_check_def`,
   `msdomain_add_storage_def`, `access_storage_split`, and associated simp
   theorems.

2. **Memory decompositions**: `memory_cost_def` (parameterized by memory list),
   `memory_expand_by_def`, `expanded_memory_def`, `memory_expansion_info_split`,
   `expand_memory_split`, and associated simp theorems.

3. **Gas cost definitions**: `Keccak256_gas_def`, `CallDataCopy_gas_def`,
   `CodeCopy_gas_def`, `ReturnDataCopy_gas_def`, `MCopy_gas_def`,
   `Balance_gas_def`, `ExtCodeSize_gas_def`, `ExtCodeCopy_gas_def`,
   `ExtCodeHash_gas_def`.

4. **SSTORE decomposition**: `sstore_refund_updates_def`,
   `sstore_base_gas_def`, `SStore_gas_def`,
   `sstore_write_accounts_updater_def`, `SStore_write_def`.

5. **Misc helpers**: `with_zero_mod_def`, `exponent_byte_size_def`,
   `exp_cost_def`, `MCopy_write_def`, `rollback_with_tStorage_simp`.

### Move `modexp_def` out of `vfmExecutionScript.sml`

Modular exponentiation for the MODEXP precompile, sitting at line 9 with a
TODO. Belongs in a math utility or precompiles theory.

### Move monad simp lemmas out of `vfmExecutionPropScript.sml`

`execution` type alias, `return_bind`, `return_ignore_bind`, etc. at line 36.
General monad infrastructure that could live closer to the monad definition.

### Factor out duplicated dequeue logic

`dequeue_withdrawal_requests_def` and `dequeue_consolidation_requests_def` in
`vfmExecutionScript.sml` are nearly identical in structure. They could share a
common abstraction parameterized by contract address, target, max, and the
slot-reading function.

### Split `vfmExecutionScript.sml` (~2100 lines)

This file contains the monad definitions, all instruction implementations, all
precompiles, call/create logic, block processing, and the transaction runner.
Splitting precompiles into their own theory and separating block-level
processing from EVM step semantics would improve navigability.

## 🟢 Low Priority

### Move `fCARD_num_cv_rep` out of `vfmComputeScript.sml`

cv rep theorem for finite set cardinality, at line 14 with a TODO.

### Move `SUM_less_EVERY_less` out of `recursiveLengthPrefixScript.sml`

Generic list lemma at line 10 with a TODO.

### Move `INDEX_OF_pre` out of `contractABIScript.sml`

cv_pre theorem at line 1617 with a TODO.

### Add high-level documentation comments to spec files

The core spec files (`vfmExecutionScript.sml`, `vfmContextScript.sml`, etc.)
have almost no comments explaining the high-level design. A reader unfamiliar
with the EVM would struggle to understand the architecture (monadic execution
model, context stack for nested calls, rollback mechanism, domain tracking).
