Theory vfmTestDefs0000[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/berlin/eip2929_gas_cost_increases/test_call_insufficient_balance.json";
val defs = mapi (define_test "0000") tests;
