Theory vfmTestDefs1528[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest313.json";
val defs = mapi (define_test "1528") tests;
