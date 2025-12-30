Theory vfmTestDefs1099[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log4_nonEmptyMem.json";
val defs = mapi (define_test "1099") tests;
