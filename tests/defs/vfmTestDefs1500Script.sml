Theory vfmTestDefs1500[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest288.json";
val defs = mapi (define_test "1500") tests;
