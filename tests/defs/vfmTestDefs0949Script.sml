Theory vfmTestDefs0949[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/eip2929.json";
val defs = mapi (define_test "0949") tests;
