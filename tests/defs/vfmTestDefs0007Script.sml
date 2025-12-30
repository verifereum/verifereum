Theory vfmTestDefs0007[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/byzantium/eip196_ec_add_mul/test_gas_costs.json";
val defs = mapi (define_test "0007") tests;
