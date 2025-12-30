Theory vfmTestDefs2244[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcallcode_001_OOGMAfter.json";
val defs = mapi (define_test "2244") tests;
