Theory vfmTestDefs1673[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_0to_xto0/sstore_0to_xto0.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_0to_xto0/sstore_0to_xto0.json");
val defs = mapi (define_test "1673") tests;
