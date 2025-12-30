Theory vfmTestDefs1135[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/MSTORE_Bounds2.json";
val defs = mapi (define_test "1135") tests;
