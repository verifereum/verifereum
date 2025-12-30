Theory vfmTestDefs1148[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/static_CALL_Bounds2a.json";
val defs = mapi (define_test "1148") tests;
