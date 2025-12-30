Theory vfmTestDefs0086[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_sufficient_balance_blob_tx_pre_fund_tx.json";
val defs = mapi (define_test "0086") tests;
