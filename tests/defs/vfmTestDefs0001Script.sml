Theory vfmTestDefs0001[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/berlin/eip2929_gas_cost_increases/test_precompile_warming.json";
val defs = mapi (define_test "0001") tests;
