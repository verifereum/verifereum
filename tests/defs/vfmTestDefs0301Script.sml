Theory vfmTestDefs0301[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_authorization_reusing_nonce.json";
val defs = mapi (define_test "0301") tests;
