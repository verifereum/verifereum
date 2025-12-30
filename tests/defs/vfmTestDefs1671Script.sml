Theory vfmTestDefs1671[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest421.json";
val defs = mapi (define_test "1671") tests;
