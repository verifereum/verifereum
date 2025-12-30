Theory vfmTestDefs0948[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/eip2929-ff.json";
val defs = mapi (define_test "0948") tests;
