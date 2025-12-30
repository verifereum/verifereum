Theory vfmTestDefs2727[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_0-0_0-0_25000_80.json";
val defs = mapi (define_test "2727") tests;
