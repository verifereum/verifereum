Theory vfmTestDefs0062[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_blob_gas_used_in_header.json";
val defs = mapi (define_test "0062") tests;
