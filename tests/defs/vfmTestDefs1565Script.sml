Theory vfmTestDefs1565[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest357.json";
val defs = mapi (define_test "1565") tests;
