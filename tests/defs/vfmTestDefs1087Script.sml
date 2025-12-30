Theory vfmTestDefs1087[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log3_logMemsizeTooHigh.json";
val defs = mapi (define_test "1087") tests;
