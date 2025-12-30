Theory vfmTestDefs0191[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_modexp_invalid_inputs.json";
val defs = mapi (define_test "0191") tests;
