Theory vfmTestDefs1529[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest315.json";
val defs = mapi (define_test "1529") tests;
