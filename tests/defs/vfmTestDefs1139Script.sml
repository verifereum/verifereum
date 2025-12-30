Theory vfmTestDefs1139[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/SLOAD_Bounds.json";
val defs = mapi (define_test "1139") tests;
