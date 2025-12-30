Theory vfmTestDefs1439[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest217.json";
val defs = mapi (define_test "1439") tests;
