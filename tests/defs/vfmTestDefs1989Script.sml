Theory vfmTestDefs1989[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_XtoY.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSStoreTest/sstore_XtoY.json");
val defs = mapi (define_test "1989") tests;
