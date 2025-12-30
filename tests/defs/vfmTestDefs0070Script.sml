Theory vfmTestDefs0070[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_inputs.json";
val defs = mapi (define_test "0070") tests;
