Theory vfmTestDefs2368[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_refund_CallToSuicideNoStorage.json";
val defs = mapi (define_test "2368") tests;
