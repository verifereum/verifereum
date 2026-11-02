Theory vfmTestDefs0750[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/access_list_gas/access_list_duplicate_address_key_intrinsic_and_warmth.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/access_list_gas/access_list_duplicate_address_key_intrinsic_and_warmth.json");
val defs = mapi (define_test "0750") tests;
