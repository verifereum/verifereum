Theory vfmTestDefs2117[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallAskMoreGasOnDepth2ThenTransactionHas.json";
val defs = mapi (define_test "2117") tests;
