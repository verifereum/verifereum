Theory vfmTestDefs0006[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/berlin/eip2930_access_list/test_tx_intrinsic_gas.json";
val defs = mapi (define_test "0006") tests;
