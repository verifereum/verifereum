Theory vfmTestDefs2495[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/TransactionToItself.json";
val defs = mapi (define_test "2495") tests;
