Theory vfmTestDefs2791[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-0_9935_28000_96.json";
val defs = mapi (define_test "2791") tests;
