Theory vfmTestDefs0945[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawExtCodeCopyGas.json";
val defs = mapi (define_test "0945") tests;
