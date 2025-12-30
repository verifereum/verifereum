Theory vfmTestDefs1832[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest620.json";
val defs = mapi (define_test "1832") tests;
