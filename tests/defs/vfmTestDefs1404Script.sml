Theory vfmTestDefs1404[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest18.json";
val defs = mapi (define_test "1404") tests;
