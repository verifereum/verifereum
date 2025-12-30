Theory vfmTestDefs0937[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCreateGas.json";
val defs = mapi (define_test "0937") tests;
