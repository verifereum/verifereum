Theory vfmTestDefs2240[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcallcode_001.json";
val defs = mapi (define_test "2240") tests;
