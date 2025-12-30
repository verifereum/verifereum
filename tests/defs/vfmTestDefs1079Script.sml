Theory vfmTestDefs1079[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_nonEmptyMem.json";
val defs = mapi (define_test "1079") tests;
