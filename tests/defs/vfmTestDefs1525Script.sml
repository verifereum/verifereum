Theory vfmTestDefs1525[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest310.json";
val defs = mapi (define_test "1525") tests;
