Theory vfmTestDefs0087[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_tx_entry_point.json";
val defs = mapi (define_test "0087") tests;
