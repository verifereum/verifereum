Theory vfmTestDefs1821[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest604.json";
val defs = mapi (define_test "1821") tests;
