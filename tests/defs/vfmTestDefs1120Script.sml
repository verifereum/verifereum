Theory vfmTestDefs1120[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CREATE_Bounds.json";
val defs = mapi (define_test "1120") tests;
