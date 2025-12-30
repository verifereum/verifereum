Theory vfmTestDefs0082[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_precompile_before_fork.json";
val defs = mapi (define_test "0082") tests;
