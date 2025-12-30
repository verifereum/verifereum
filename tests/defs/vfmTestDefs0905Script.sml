Theory vfmTestDefs0905[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/CallAskMoreGasOnDepth2ThenTransactionHas.json";
val defs = mapi (define_test "0905") tests;
