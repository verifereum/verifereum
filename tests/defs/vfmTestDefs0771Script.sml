Theory vfmTestDefs0771[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/call_gas/repeated_value_call_to_same_recipient.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/call_gas/repeated_value_call_to_same_recipient.json");
val defs = mapi (define_test "0771") tests;
