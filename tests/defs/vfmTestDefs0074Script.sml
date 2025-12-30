Theory vfmTestDefs0074[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_post_fork_block_without_blob_fields.json";
val defs = mapi (define_test "0074") tests;
