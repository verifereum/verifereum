Theory vfmTestDefs2469[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/HighGasPriceParis.json";
val defs = mapi (define_test "2469") tests;
