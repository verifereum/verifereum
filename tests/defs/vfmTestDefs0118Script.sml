Theory vfmTestDefs0118[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/create/test_create_deposit_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/create/test_create_deposit_oog.json");
val defs = mapi (define_test "0118") tests;
