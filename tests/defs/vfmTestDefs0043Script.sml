Theory vfmTestDefs0043[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_blob_tx_attribute_gasprice_opcode.json";
val defs = mapi (define_test "0043") tests;
