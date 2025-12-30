Theory vfmTestDefs0190[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_modexp_gas_usage_contract_wrapper.json";
val defs = mapi (define_test "0190") tests;
