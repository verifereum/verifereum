Theory vfmTestDefs1418[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest196.json";
val defs = mapi (define_test "1418") tests;
