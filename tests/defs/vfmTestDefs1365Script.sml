Theory vfmTestDefs1365[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest138.json";
val defs = mapi (define_test "1365") tests;
