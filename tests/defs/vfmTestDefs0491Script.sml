Theory vfmTestDefs0491[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/block_2d_gas_accounting/cumulative_block_state_gas_boundary.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/block_2d_gas_accounting/cumulative_block_state_gas_boundary.json");
val defs = mapi (define_test "0491") tests;
