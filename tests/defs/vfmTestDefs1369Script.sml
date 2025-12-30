Theory vfmTestDefs1369[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest143.json";
val defs = mapi (define_test "1369") tests;
