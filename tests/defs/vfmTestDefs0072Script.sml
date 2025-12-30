Theory vfmTestDefs0072[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_non_multiple_excess_blob_gas.json";
val defs = mapi (define_test "0072") tests;
