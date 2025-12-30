Theory vfmTestDefs2468[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/HighGasLimit.json";
val defs = mapi (define_test "2468") tests;
