Theory vfmTestDefs1638[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest98.json";
val defs = mapi (define_test "1638") tests;
