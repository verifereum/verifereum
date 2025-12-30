Theory vfmTestDefs0957[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/gasCostReturn.json";
val defs = mapi (define_test "0957") tests;
