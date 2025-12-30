Theory vfmTestDefs0010[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_basic_tload_after_store.json";
val defs = mapi (define_test "0010") tests;
