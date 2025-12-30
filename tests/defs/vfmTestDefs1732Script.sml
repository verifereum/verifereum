Theory vfmTestDefs1732[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest496.json";
val defs = mapi (define_test "1732") tests;
