Theory vfmTestDefs1472[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest259.json";
val defs = mapi (define_test "1472") tests;
