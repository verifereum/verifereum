Theory vfmTestDefs1059[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log0_logMemsizeTooHigh.json";
val defs = mapi (define_test "1059") tests;
