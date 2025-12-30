Theory vfmTestDefs0220[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7939_count_leading_zeros/test_clz_with_memory_operation.json";
val defs = mapi (define_test "0220") tests;
