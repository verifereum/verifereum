Theory vfmTestDefs0355[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_multiple_valid_authorization_tuples_first_invalid_same_signer.json";
val defs = mapi (define_test "0355") tests;
