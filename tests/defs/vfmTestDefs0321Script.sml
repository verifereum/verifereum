Theory vfmTestDefs0321[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_eoa_tx_after_set_code.json";
val defs = mapi (define_test "0321") tests;
