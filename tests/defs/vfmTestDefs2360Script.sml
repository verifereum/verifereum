Theory vfmTestDefs2360[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_log1_MaxTopic.json";
val defs = mapi (define_test "2360") tests;
