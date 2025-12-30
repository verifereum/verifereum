Theory vfmTestDefs1637[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest97.json";
val defs = mapi (define_test "1637") tests;
