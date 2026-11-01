Theory vfmTestDefs0810[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/set_code_auth_gas/auth_execution_intrinsic_magnitude.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/set_code_auth_gas/auth_execution_intrinsic_magnitude.json");
val defs = mapi (define_test "0810") tests;
