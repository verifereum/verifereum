Theory vfmTestDefs1800[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest577.json";
val defs = mapi (define_test "1800") tests;
