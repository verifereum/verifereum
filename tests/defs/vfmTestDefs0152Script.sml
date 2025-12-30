Theory vfmTestDefs0152[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/validation/test_tx_gas_limit.json";
val defs = mapi (define_test "0152") tests;
