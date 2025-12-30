Theory vfmTestDefs0217[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7939_count_leading_zeros/test_clz_push_operation_same_value.json";
val defs = mapi (define_test "0217") tests;
