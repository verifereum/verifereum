Theory vfmTestDefs0388[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3860_initcode/test_gas_usage.json";
val defs = mapi (define_test "0388") tests;
