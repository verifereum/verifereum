Theory vfmTestDefs0210[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7939_count_leading_zeros/test_clz_gas_cost.json";
val defs = mapi (define_test "0210") tests;
