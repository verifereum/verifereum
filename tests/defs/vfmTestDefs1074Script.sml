Theory vfmTestDefs1074[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_MaxTopic.json";
val defs = mapi (define_test "1074") tests;
