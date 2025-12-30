Theory vfmTestDefs1389[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest163.json";
val defs = mapi (define_test "1389") tests;
