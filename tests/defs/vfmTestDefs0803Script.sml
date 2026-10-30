Theory vfmTestDefs0803[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/selfdestruct_gas/selfdestruct_new_beneficiary_execution_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/selfdestruct_gas/selfdestruct_new_beneficiary_execution_gas.json");
val defs = mapi (define_test "0803") tests;
