Theory vfmTestDefs1217[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/stackLimitPush31_1025.json";
val defs = mapi (define_test "1217") tests;
