Theory vfmTestDefs1354[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest124.json";
val defs = mapi (define_test "1354") tests;
