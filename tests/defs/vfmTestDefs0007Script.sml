Theory vfmTestDefs0007[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/berlin/eip2930_access_list/acl/account_storage_warm_cold_state.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/berlin/eip2930_access_list/acl/account_storage_warm_cold_state.json");
val defs = mapi (define_test "0007") tests;
