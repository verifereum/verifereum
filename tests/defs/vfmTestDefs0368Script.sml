Theory vfmTestDefs0368[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_to_sstore_then_sload.json";
val defs = mapi (define_test "0368") tests;
