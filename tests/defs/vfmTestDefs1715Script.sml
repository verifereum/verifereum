Theory vfmTestDefs1715[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest475.json";
val defs = mapi (define_test "1715") tests;
