Theory vfmTestDefs0048[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_blobhash_invalid_blob_index.json";
val defs = mapi (define_test "0048") tests;
