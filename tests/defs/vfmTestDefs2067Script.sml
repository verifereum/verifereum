Theory vfmTestDefs2067[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/failed_tx_xcf416c53_Paris.json";
val defs = mapi (define_test "2067") tests;
