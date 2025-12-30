Theory vfmTestDefs1128[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/JUMPI_Bounds.json";
val defs = mapi (define_test "1128") tests;
