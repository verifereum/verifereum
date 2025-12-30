Theory vfmTestDefs0003[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/berlin/eip2930_access_list/test_eip2930_tx_validity.json";
val defs = mapi (define_test "0003") tests;
