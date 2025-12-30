Theory vfmTestDefs0165[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7594_peerdas/test_invalid_max_blobs_per_tx.json";
val defs = mapi (define_test "0165") tests;
