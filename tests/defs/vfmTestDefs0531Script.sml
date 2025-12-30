Theory vfmTestDefs0531[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/operationDiffGas.json";
val defs = mapi (define_test "0531") tests;
