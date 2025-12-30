Theory vfmTestDefs1210[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/oog.json";
val defs = mapi (define_test "1210") tests;
