Theory vfmTestDefs0160[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/istanbul/eip152_blake2/test_blake2b_gas_limit.json";
val defs = mapi (define_test "0160") tests;
