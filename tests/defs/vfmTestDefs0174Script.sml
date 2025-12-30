Theory vfmTestDefs0174[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7825_transaction_gas_limit_cap/test_transaction_gas_limit_cap_at_transition.json";
val defs = mapi (define_test "0174") tests;
