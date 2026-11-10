Theory vfmTestDefs0490[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/block_2d_gas_accounting/block_gas_used_state_dominates.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/block_2d_gas_accounting/block_gas_used_state_dominates.json");
val defs = mapi (define_test "0490") tests;
