Theory vfmTestDefs1329[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest0.json";
val defs = mapi (define_test "1329") tests;
