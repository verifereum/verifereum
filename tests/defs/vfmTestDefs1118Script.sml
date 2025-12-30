Theory vfmTestDefs1118[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CALL_Bounds2a.json";
val defs = mapi (define_test "1118") tests;
