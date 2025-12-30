Theory vfmTestDefs1333[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest102.json";
val defs = mapi (define_test "1333") tests;
