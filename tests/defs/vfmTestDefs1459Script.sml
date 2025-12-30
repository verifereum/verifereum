Theory vfmTestDefs1459[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest243.json";
val defs = mapi (define_test "1459") tests;
