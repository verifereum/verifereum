Theory vfmTestDefs0019[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_run_until_out_of_gas.json";
val defs = mapi (define_test "0019") tests;
