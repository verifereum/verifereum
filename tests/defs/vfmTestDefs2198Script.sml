Theory vfmTestDefs2198[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_ReturnTest.json";
val defs = mapi (define_test "2198") tests;
