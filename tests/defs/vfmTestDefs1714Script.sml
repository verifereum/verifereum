Theory vfmTestDefs1714[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest474.json";
val defs = mapi (define_test "1714") tests;
