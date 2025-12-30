Theory vfmTestDefs1123[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/DELEGATECALL_Bounds.json";
val defs = mapi (define_test "1123") tests;
