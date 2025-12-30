Theory vfmTestDefs0067[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_excess_blob_gas_above_target_change.json";
val defs = mapi (define_test "0067") tests;
