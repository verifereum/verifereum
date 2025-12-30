Theory vfmTestDefs1543[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest334.json";
val defs = mapi (define_test "1543") tests;
