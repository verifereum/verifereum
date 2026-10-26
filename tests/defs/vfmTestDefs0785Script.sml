Theory vfmTestDefs0785[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/eip_mainnet/selfdestruct_funds_new_account.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8038_state_access_gas_cost_increase/eip_mainnet/selfdestruct_funds_new_account.json");
val defs = mapi (define_test "0785") tests;
