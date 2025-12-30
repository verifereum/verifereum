Theory vfmTestDefs1471[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest257.json";
val defs = mapi (define_test "1471") tests;
