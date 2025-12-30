Theory vfmTestDefs1593[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest41.json";
val defs = mapi (define_test "1593") tests;
