Theory vfmTestDefs2798[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-3_0_21000_80.json";
val defs = mapi (define_test "2798") tests;
