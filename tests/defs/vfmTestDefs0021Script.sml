Theory vfmTestDefs0021[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_tload_after_sstore.json";
val defs = mapi (define_test "0021") tests;
