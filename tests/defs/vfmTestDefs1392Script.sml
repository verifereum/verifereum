Theory vfmTestDefs1392[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest167.json";
val defs = mapi (define_test "1392") tests;
