Theory vfmTestDefs1497[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest285.json";
val defs = mapi (define_test "1497") tests;
