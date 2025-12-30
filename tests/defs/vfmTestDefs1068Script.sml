Theory vfmTestDefs1068[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log1_logMemsizeTooHigh.json";
val defs = mapi (define_test "1068") tests;
