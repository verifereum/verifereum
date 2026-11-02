Theory vfmTestDefs0787[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/exact_balance_no_fallback/access_list_no_fallback.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/exact_balance_no_fallback/access_list_no_fallback.json");
val defs = mapi (define_test "0787") tests;
