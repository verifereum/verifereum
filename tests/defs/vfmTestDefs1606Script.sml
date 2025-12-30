Theory vfmTestDefs1606[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest57.json";
val defs = mapi (define_test "1606") tests;
