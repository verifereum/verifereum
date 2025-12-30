Theory vfmTestDefs0084[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_reject_valid_full_blob_in_block_rlp.json";
val defs = mapi (define_test "0084") tests;
