Theory vfmTestDefs1496[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest283.json";
val defs = mapi (define_test "1496") tests;
