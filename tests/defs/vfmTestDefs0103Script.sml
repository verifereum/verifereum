Theory vfmTestDefs0103[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_recreate_self_destructed_contract_different_txs.json";
val defs = mapi (define_test "0103") tests;
