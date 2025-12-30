Theory vfmTestDefs2601[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-2_9935_21000_96.json";
val defs = mapi (define_test "2601") tests;
