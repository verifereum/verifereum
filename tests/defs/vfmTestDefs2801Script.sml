Theory vfmTestDefs2801[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-3_0_28000_64.json";
val defs = mapi (define_test "2801") tests;
