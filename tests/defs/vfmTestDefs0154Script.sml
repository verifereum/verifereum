Theory vfmTestDefs0154[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/homestead/coverage/test_coverage.json";
val defs = mapi (define_test "0154") tests;
