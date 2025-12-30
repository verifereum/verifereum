Theory vfmTestDefs1772[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest542.json";
val defs = mapi (define_test "1772") tests;
