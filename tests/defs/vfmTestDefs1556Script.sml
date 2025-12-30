Theory vfmTestDefs1556[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest348.json";
val defs = mapi (define_test "1556") tests;
