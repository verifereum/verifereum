Theory vfmTestDefs2729[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_0-0_1-2_21000_192.json";
val defs = mapi (define_test "2729") tests;
