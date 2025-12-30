Theory vfmTestDefs1791[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest565.json";
val defs = mapi (define_test "1791") tests;
