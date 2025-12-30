Theory vfmTestDefs1420[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest198.json";
val defs = mapi (define_test "1420") tests;
