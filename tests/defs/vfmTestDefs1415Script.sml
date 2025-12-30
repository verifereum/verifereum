Theory vfmTestDefs1415[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest192.json";
val defs = mapi (define_test "1415") tests;
