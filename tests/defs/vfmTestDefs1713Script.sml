Theory vfmTestDefs1713[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest473.json";
val defs = mapi (define_test "1713") tests;
