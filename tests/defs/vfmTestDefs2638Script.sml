Theory vfmTestDefs2638[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-3_9935_21000_128.json";
val defs = mapi (define_test "2638") tests;
