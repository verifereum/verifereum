Theory vfmTestDefs2750[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_1145-3932_2969-1336_21000_128.json";
val defs = mapi (define_test "2750") tests;
