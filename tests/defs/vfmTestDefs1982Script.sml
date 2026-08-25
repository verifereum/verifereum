Theory vfmTestDefs1982[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_Xto0toX.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSStoreTest/sstore_Xto0toX.json");
val defs = mapi (define_test "1982") tests;
