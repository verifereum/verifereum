Theory vfmTestDefs0011[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_basic_tload_gasprice.json";
val defs = mapi (define_test "0011") tests;
