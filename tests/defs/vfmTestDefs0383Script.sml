Theory vfmTestDefs0383[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3651_warm_coinbase/test_warm_coinbase_gas_usage.json";
val defs = mapi (define_test "0383") tests;
