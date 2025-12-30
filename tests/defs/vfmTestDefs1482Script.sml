Theory vfmTestDefs1482[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest269.json";
val defs = mapi (define_test "1482") tests;
