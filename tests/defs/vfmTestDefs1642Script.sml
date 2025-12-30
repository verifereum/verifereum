Theory vfmTestDefs1642[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest386.json";
val defs = mapi (define_test "1642") tests;
