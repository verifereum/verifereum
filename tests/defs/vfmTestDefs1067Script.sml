Theory vfmTestDefs1067[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log1_logMemStartTooHigh.json";
val defs = mapi (define_test "1067") tests;
