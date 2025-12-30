Theory vfmTestDefs2037[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shr_-1_256.json";
val defs = mapi (define_test "2037") tests;
