Theory vfmTestDefs1096[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log4_logMemStartTooHigh.json";
val defs = mapi (define_test "1096") tests;
