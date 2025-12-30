Theory vfmTestDefs0940[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCreateGasValueTransferMemory.json";
val defs = mapi (define_test "0940") tests;
