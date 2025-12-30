Theory vfmTestDefs1508[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest296.json";
val defs = mapi (define_test "1508") tests;
