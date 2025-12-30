Theory vfmTestDefs1627[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest84.json";
val defs = mapi (define_test "1627") tests;
