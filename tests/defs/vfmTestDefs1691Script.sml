Theory vfmTestDefs1691[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_xto_yto0/sstore_xto_yto0.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_xto_yto0/sstore_xto_yto0.json");
val defs = mapi (define_test "1691") tests;
