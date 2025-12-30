Theory vfmTestDefs0327[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_gas_diff_pointer_vs_direct_call.json";
val defs = mapi (define_test "0327") tests;
