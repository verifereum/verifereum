Theory vfmTestDefs2471[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stSpecialTest/failed_tx_xcf416c53_paris/failed_tx_xcf416c53_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stSpecialTest/failed_tx_xcf416c53_paris/failed_tx_xcf416c53_paris.json");
val defs = mapi (define_test "2471") tests;
