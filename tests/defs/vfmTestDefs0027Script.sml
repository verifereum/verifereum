Theory vfmTestDefs0027[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_tstore_clear_after_deployment_tx.json";
val defs = mapi (define_test "0027") tests;
