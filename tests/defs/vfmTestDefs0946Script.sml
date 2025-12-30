Theory vfmTestDefs0946[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawExtCodeCopyMemoryGas.json";
val defs = mapi (define_test "0946") tests;
