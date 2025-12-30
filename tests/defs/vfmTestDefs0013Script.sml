Theory vfmTestDefs0013[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_basic_tload_transaction_begin.json";
val defs = mapi (define_test "0013") tests;
