Theory vfmTestDefs1384[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest158.json";
val defs = mapi (define_test "1384") tests;
