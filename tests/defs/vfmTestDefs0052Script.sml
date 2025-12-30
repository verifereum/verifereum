Theory vfmTestDefs0052[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_blobhash_scenarios.json";
val defs = mapi (define_test "0052") tests;
