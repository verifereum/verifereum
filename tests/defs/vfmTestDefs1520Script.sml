Theory vfmTestDefs1520[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest306.json";
val defs = mapi (define_test "1520") tests;
