Theory vfmTestDefs2717[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/pointMulAdd2.json";
val defs = mapi (define_test "2717") tests;
