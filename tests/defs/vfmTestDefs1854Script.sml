Theory vfmTestDefs1854[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest646.json";
val defs = mapi (define_test "1854") tests;
