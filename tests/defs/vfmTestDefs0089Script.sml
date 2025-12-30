Theory vfmTestDefs0089[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_valid_inputs.json";
val defs = mapi (define_test "0089") tests;
