Theory vfmTestDefs0079[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_tx_max_fee_per_blob_gas.json";
val defs = mapi (define_test "0079") tests;
