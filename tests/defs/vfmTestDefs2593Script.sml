Theory vfmTestDefs2593[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-2_5616_21000_96.json";
val defs = mapi (define_test "2593") tests;
