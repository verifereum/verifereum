Theory vfmTestDefs0041[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_blob_gas_subtraction_tx.json";
val defs = mapi (define_test "0041") tests;
