Theory vfmTestDefs0005[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/berlin/eip2930_access_list/test_transaction_intrinsic_gas_cost.json";
val defs = mapi (define_test "0005") tests;
