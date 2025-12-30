Theory vfmTestDefs2476[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/NoSrcAccount1559.json";
val defs = mapi (define_test "2476") tests;
