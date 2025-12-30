Theory vfmTestDefs1602[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest52.json";
val defs = mapi (define_test "1602") tests;
