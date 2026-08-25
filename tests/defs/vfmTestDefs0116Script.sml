Theory vfmTestDefs0116[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/constantinople/eip1014_create2/test_recreate.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/constantinople/eip1014_create2/test_recreate.json");
val defs = mapi (define_test "0116") tests;
