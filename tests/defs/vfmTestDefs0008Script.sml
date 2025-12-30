Theory vfmTestDefs0008[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/byzantium/eip197_ec_pairing/test_gas_costs.json";
val defs = mapi (define_test "0008") tests;
