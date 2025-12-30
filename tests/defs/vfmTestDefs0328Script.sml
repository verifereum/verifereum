Theory vfmTestDefs0328[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_intrinsic_gas_cost.json";
val defs = mapi (define_test "0328") tests;
