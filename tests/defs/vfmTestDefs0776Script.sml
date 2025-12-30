Theory vfmTestDefs0776[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stChainId/chainIdGasCost.json";
val defs = mapi (define_test "0776") tests;
