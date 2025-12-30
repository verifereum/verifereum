Theory vfmTestDefs2645[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-3_9_28000_96.json";
val defs = mapi (define_test "2645") tests;
