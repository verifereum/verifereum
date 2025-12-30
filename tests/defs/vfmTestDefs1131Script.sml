Theory vfmTestDefs1131[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/MLOAD_Bounds.json";
val defs = mapi (define_test "1131") tests;
