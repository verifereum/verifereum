Theory vfmTestDefs1686[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest442.json";
val defs = mapi (define_test "1686") tests;
