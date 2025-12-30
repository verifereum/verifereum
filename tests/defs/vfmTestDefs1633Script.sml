Theory vfmTestDefs1633[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest90.json";
val defs = mapi (define_test "1633") tests;
