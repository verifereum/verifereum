Theory vfmTestDefs1523[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest309.json";
val defs = mapi (define_test "1523") tests;
