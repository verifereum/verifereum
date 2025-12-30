Theory vfmTestDefs1098[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log4_logMemsizeZero.json";
val defs = mapi (define_test "1098") tests;
