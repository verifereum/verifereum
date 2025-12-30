Theory vfmTestDefs2483[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/StoreClearsAndInternalCallStoreClearsSuccess.json";
val defs = mapi (define_test "2483") tests;
