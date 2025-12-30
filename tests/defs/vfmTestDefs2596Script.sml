Theory vfmTestDefs2596[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-2_5617_21000_96.json";
val defs = mapi (define_test "2596") tests;
