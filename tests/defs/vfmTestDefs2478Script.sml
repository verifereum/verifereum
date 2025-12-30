Theory vfmTestDefs2478[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/NoSrcAccountCreate1559.json";
val defs = mapi (define_test "2478") tests;
