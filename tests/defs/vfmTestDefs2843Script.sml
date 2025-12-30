Theory vfmTestDefs2843[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_1-2_1_21000_96.json";
val defs = mapi (define_test "2843") tests;
