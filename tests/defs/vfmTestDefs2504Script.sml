Theory vfmTestDefs2504[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/dayLimitConstructionPartial.json";
val defs = mapi (define_test "2504") tests;
