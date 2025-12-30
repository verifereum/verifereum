Theory vfmTestDefs1970[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/SstoreCallToSelfSubRefundBelowZero.json";
val defs = mapi (define_test "1970") tests;
