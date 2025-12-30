Theory vfmTestDefs1462[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest246.json";
val defs = mapi (define_test "1462") tests;
