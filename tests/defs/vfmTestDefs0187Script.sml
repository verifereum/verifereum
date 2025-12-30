Theory vfmTestDefs0187[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_modexp_call_operations.json";
val defs = mapi (define_test "0187") tests;
