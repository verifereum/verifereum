Theory vfmTestDefs2741[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_1-2_0-0_25000_64.json";
val defs = mapi (define_test "2741") tests;
