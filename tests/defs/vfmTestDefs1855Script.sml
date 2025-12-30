Theory vfmTestDefs1855[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest647.json";
val defs = mapi (define_test "1855") tests;
