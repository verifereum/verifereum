Theory vfmTestDefs0944[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawDelegateCallGasMemoryAsk.json";
val defs = mapi (define_test "0944") tests;
