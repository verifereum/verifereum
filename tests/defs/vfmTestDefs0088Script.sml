Theory vfmTestDefs0088[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_valid_blob_tx_combinations.json";
val defs = mapi (define_test "0088") tests;
