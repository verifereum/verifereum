Theory vfmTestDefs1101[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log4_nonEmptyMem_logMemSize1_logMemStart31.json";
val defs = mapi (define_test "1101") tests;
