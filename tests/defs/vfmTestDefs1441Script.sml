Theory vfmTestDefs1441[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest22.json";
val defs = mapi (define_test "1441") tests;
