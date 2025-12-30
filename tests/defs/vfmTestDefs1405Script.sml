Theory vfmTestDefs1405[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest180.json";
val defs = mapi (define_test "1405") tests;
