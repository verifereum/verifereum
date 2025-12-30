Theory vfmTestDefs0931[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCallGasValueTransferMemory.json";
val defs = mapi (define_test "0931") tests;
