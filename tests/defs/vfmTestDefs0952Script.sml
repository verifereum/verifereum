Theory vfmTestDefs0952[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/gasCostBerlin.json";
val defs = mapi (define_test "0952") tests;
