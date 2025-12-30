Theory vfmTestDefs2720[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_0-0_0-0_21000_192.json";
val defs = mapi (define_test "2720") tests;
