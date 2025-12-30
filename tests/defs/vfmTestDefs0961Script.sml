Theory vfmTestDefs0961[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/lowGasLimit.json";
val defs = mapi (define_test "0961") tests;
