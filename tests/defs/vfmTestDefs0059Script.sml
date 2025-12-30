Theory vfmTestDefs0059[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_fork_transition_excess_blob_gas_post_blob_genesis.json";
val defs = mapi (define_test "0059") tests;
