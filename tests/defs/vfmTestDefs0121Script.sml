Theory vfmTestDefs0121[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/create/test_create_suicide_store.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/create/test_create_suicide_store.json");
val defs = mapi (define_test "0121") tests;
