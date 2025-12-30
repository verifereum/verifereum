Theory vfmTestDefs1545[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest336.json";
val defs = mapi (define_test "1545") tests;
