Theory vfmTestDefs2749[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_1145-3932_1145-4651_25000_192.json";
val defs = mapi (define_test "2749") tests;
