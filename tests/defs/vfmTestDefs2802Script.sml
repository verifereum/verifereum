Theory vfmTestDefs2802[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-3_0_28000_80.json";
val defs = mapi (define_test "2802") tests;
