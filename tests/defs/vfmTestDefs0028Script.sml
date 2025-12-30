Theory vfmTestDefs0028[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_tstore_clear_after_tx.json";
val defs = mapi (define_test "0028") tests;
