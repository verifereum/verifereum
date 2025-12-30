Theory vfmTestDefs2219[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callWithHighValue.json";
val defs = mapi (define_test "2219") tests;
