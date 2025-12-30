Theory vfmTestDefs0046[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_blob_type_tx_pre_fork.json";
val defs = mapi (define_test "0046") tests;
