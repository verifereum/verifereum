Theory vfmTestDefs0194[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_modexp_variable_gas_cost_exceed_tx_gas_cap.json";
val defs = mapi (define_test "0194") tests;
