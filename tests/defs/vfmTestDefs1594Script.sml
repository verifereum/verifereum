Theory vfmTestDefs1594[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest42.json";
val defs = mapi (define_test "1594") tests;
