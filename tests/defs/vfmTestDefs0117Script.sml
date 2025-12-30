Theory vfmTestDefs0117[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/constantinople/eip145_bitwise_shift/test_combinations.json";
val defs = mapi (define_test "0117") tests;
