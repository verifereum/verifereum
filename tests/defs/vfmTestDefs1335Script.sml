Theory vfmTestDefs1335[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest104.json";
val defs = mapi (define_test "1335") tests;
