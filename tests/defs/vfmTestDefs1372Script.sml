Theory vfmTestDefs1372[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest146.json";
val defs = mapi (define_test "1372") tests;
