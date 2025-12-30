Theory vfmTestDefs0923[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCallCodeGasValueTransfer.json";
val defs = mapi (define_test "0923") tests;
