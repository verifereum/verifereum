Theory vfmTestDefs1089[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log3_nonEmptyMem.json";
val defs = mapi (define_test "1089") tests;
