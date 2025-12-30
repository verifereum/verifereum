Theory vfmTestDefs1138[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/RETURN_Bounds.json";
val defs = mapi (define_test "1138") tests;
