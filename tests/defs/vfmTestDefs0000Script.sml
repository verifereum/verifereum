Theory vfmTestDefs0000[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/amsterdam/eip8037_state_creation_gas_cost_increase/block_2d_gas_accounting/tx_inclusion_at_execution_gas_block_limit_small.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/amsterdam/eip8037_state_creation_gas_cost_increase/block_2d_gas_accounting/tx_inclusion_at_execution_gas_block_limit_small.json");
val defs = mapi (define_test "0000") tests;
