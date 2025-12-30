Theory vfmTestDefs0016[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_gas_usage.json";
val defs = mapi (define_test "0016") tests;
