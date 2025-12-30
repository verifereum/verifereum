Theory vfmTestDefs1669[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest419.json";
val defs = mapi (define_test "1669") tests;
