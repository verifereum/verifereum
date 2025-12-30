Theory vfmTestDefs2176[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallToNameRegistrator0.json";
val defs = mapi (define_test "2176") tests;
