Theory vfmTestDefs1694[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_xto_yto_z/sstore_xto_yto_z.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_xto_yto_z/sstore_xto_yto_z.json");
val defs = mapi (define_test "1694") tests;
