Theory vfmTestDefs1436[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest214.json";
val defs = mapi (define_test "1436") tests;
