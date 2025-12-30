Theory vfmTestDefs0099[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_create_selfdestruct_same_tx_increased_nonce.json";
val defs = mapi (define_test "0099") tests;
