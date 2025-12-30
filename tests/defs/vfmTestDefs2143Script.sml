Theory vfmTestDefs2143[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallIdentity_2.json";
val defs = mapi (define_test "2143") tests;
