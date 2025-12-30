Theory vfmTestDefs0290[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/test_gas_consumption_below_data_floor.json";
val defs = mapi (define_test "0290") tests;
