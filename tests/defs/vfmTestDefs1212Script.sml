Theory vfmTestDefs1212[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/stackLimitGas_1023.json";
val defs = mapi (define_test "1212") tests;
