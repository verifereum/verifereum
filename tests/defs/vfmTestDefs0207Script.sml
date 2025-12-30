Theory vfmTestDefs0207[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7939_count_leading_zeros/test_clz_code_copy_operation.json";
val defs = mapi (define_test "0207") tests;
