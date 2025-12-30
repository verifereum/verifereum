Theory vfmTestDefs2492[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/TransactionSendingToEmpty.json";
val defs = mapi (define_test "2492") tests;
