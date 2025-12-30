Theory vfmTestDefs0289[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/test_full_gas_consumption.json";
val defs = mapi (define_test "0289") tests;
