Theory vfmTestDefs1218[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/stackLimitPush32_1023.json";
val defs = mapi (define_test "1218") tests;
