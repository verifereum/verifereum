Theory vfmTestDefs1502[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest290.json";
val defs = mapi (define_test "1502") tests;
