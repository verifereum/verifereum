Theory vfmTestDefs0064[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_blob_hash_versioning_single_tx.json";
val defs = mapi (define_test "0064") tests;
