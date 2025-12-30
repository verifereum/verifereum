Theory vfmTestDefs1093[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log4_MaxTopic.json";
val defs = mapi (define_test "1093") tests;
