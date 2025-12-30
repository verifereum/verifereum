Theory vfmTestDefs0150[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/validation/test_gas_limit_below_minimum.json";
val defs = mapi (define_test "0150") tests;
