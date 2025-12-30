Theory vfmTestDefs0149[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/touch/test_zero_gas_price_and_touching.json";
val defs = mapi (define_test "0149") tests;
