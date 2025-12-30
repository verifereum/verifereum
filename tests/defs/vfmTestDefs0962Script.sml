Theory vfmTestDefs0962[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/lowGasPriceOldTypes.json";
val defs = mapi (define_test "0962") tests;
