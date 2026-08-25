Theory vfmTestDefs0002[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/berlin/eip2930_access_list/test_account_storage_warm_cold_state.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/berlin/eip2930_access_list/test_account_storage_warm_cold_state.json");
val defs = mapi (define_test "0002") tests;
