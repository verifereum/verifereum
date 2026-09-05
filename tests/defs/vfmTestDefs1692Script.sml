Theory vfmTestDefs1692[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_xto_yto_x/sstore_xto_yto_x.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_xto_yto_x/sstore_xto_yto_x.json");
val defs = mapi (define_test "1692") tests;
