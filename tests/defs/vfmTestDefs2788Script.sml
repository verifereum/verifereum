Theory vfmTestDefs2788[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-0_9935_21000_128.json";
val defs = mapi (define_test "2788") tests;
