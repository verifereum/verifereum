Theory vfmTestDefs0080[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_zero_excess_blob_gas_in_header.json";
val defs = mapi (define_test "0080") tests;
