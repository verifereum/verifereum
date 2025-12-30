Theory vfmTestDefs1078[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_logMemsizeZero.json";
val defs = mapi (define_test "1078") tests;
