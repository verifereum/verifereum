Theory vfmTestDefs2464[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/tangerine_whistle/eip150_operation_gas_costs/eip150_selfdestruct/selfdestruct_to_precompile_state_access_boundary.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/tangerine_whistle/eip150_operation_gas_costs/eip150_selfdestruct/selfdestruct_to_precompile_state_access_boundary.json");
val defs = mapi (define_test "2464") tests;
