Theory vfmTestDefs1819[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest602.json";
val defs = mapi (define_test "1819") tests;
