Theory vfmTestDefs0817[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/set_code_auth_refunds/existing_authority_no_new_account_charge.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/set_code_auth_refunds/existing_authority_no_new_account_charge.json");
val defs = mapi (define_test "0817") tests;
