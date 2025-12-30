Theory vfmTestDefs0144[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_value_transfer_gas_calculation_byzantium.json";
val defs = mapi (define_test "0144") tests;
