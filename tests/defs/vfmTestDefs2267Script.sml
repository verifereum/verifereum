Theory vfmTestDefs2267[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcodecall_010_OOGMAfter_3.json";
val defs = mapi (define_test "2267") tests;
