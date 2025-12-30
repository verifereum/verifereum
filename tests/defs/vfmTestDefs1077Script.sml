Theory vfmTestDefs1077[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_logMemsizeTooHigh.json";
val defs = mapi (define_test "1077") tests;
