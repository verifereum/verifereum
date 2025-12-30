Theory vfmTestDefs1378[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest151.json";
val defs = mapi (define_test "1378") tests;
