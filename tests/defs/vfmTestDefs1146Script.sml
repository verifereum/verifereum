Theory vfmTestDefs1146[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/static_CALL_Bounds.json";
val defs = mapi (define_test "1146") tests;
