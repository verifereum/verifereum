Theory vfmTestDefs1513[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest30.json";
val defs = mapi (define_test "1513") tests;
