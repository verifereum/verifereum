Theory vfmTestDefs1397[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest173.json";
val defs = mapi (define_test "1397") tests;
