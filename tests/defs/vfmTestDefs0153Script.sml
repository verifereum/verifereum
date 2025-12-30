Theory vfmTestDefs0153[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/validation/test_tx_nonce.json";
val defs = mapi (define_test "0153") tests;
