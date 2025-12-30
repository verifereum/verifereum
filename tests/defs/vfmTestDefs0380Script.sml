Theory vfmTestDefs0380[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_valid_tx_invalid_auth_signature.json";
val defs = mapi (define_test "0380") tests;
