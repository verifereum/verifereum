Theory vfmTestDefs2203[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_ZeroValue_SUICIDE_OOGRevert.json";
val defs = mapi (define_test "2203") tests;
