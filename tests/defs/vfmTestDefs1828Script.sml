Theory vfmTestDefs1828[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest612.json";
val defs = mapi (define_test "1828") tests;
