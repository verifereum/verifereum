Theory vfmTestDefs0098[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_create_selfdestruct_same_tx.json";
val defs = mapi (define_test "0098") tests;
