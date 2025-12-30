Theory vfmTestDefs0054[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_correct_decreasing_blob_gas_costs.json";
val defs = mapi (define_test "0054") tests;
