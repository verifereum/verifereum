Theory vfmTestDefs2399[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stSStoreTest/sstore_xto_x/sstore_xto_x.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stSStoreTest/sstore_xto_x/sstore_xto_x.json");
val defs = mapi (define_test "2399") tests;
