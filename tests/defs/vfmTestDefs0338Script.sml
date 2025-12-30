Theory vfmTestDefs0338[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_pointer_resets_an_empty_code_account_with_storage.json";
val defs = mapi (define_test "0338") tests;
