Theory vfmTestDefs1578[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest369.json";
val defs = mapi (define_test "1578") tests;
