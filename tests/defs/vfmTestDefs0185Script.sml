Theory vfmTestDefs0185[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_contract_initcode.json";
val defs = mapi (define_test "0185") tests;
