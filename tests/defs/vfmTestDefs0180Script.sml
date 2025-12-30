Theory vfmTestDefs0180[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7825_transaction_gas_limit_cap/test_tx_gas_limit_cap_contract_creation.json";
val defs = mapi (define_test "0180") tests;
