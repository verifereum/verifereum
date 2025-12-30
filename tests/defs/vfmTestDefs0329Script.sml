Theory vfmTestDefs0329[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_invalid_transaction_after_authorization.json";
val defs = mapi (define_test "0329") tests;
