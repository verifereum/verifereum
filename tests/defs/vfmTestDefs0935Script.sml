Theory vfmTestDefs0935[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCreateFailGasValueTransfer.json";
val defs = mapi (define_test "0935") tests;
