Theory vfmTestDefs0055[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_correct_excess_blob_gas_calculation.json";
val defs = mapi (define_test "0055") tests;
