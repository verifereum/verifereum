Theory vfmTestDefs0350[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_all_invalid_authorization_tuples.json";
val defs = mapi (define_test "0350") tests;
