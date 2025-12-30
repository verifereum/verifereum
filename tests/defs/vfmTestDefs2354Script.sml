Theory vfmTestDefs2354[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_log0_logMemStartTooHigh.json";
val defs = mapi (define_test "2354") tests;
