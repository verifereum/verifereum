Theory vfmTestDefs2247[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcallcode_001_OOGMAfter_3.json";
val defs = mapi (define_test "2247") tests;
