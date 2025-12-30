Theory vfmTestDefs1149[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/static_CALL_Bounds3.json";
val defs = mapi (define_test "1149") tests;
