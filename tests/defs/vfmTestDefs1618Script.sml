Theory vfmTestDefs1618[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest73.json";
val defs = mapi (define_test "1618") tests;
