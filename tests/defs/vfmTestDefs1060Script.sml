Theory vfmTestDefs1060[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log0_logMemsizeZero.json";
val defs = mapi (define_test "1060") tests;
