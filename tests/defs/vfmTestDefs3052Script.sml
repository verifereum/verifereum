Theory vfmTestDefs3052[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/prague/eip7623_increase_calldata_cost/block_gas_limit/tx_gas_limit_after_refunded_floor_bound_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/prague/eip7623_increase_calldata_cost/block_gas_limit/tx_gas_limit_after_refunded_floor_bound_tx.json");
val defs = mapi (define_test "3052") tests;
