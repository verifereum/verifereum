Theory vfmTestDefs0922[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCallCodeGasMemoryAsk.json";
val defs = mapi (define_test "0922") tests;
