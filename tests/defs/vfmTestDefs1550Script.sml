Theory vfmTestDefs1550[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest341.json";
val defs = mapi (define_test "1550") tests;
