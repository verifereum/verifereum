Theory vfmTestDefs1429[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest206.json";
val defs = mapi (define_test "1429") tests;
