Theory vfmTestDefs2494[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/TransactionToAddressh160minusOne.json";
val defs = mapi (define_test "2494") tests;
