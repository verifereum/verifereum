Theory vfmTestDefs2480[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/OverflowGasRequire2.json";
val defs = mapi (define_test "2480") tests;
