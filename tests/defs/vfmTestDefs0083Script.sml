Theory vfmTestDefs0083[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_precompile_during_fork.json";
val defs = mapi (define_test "0083") tests;
