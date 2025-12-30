Theory vfmTestDefs0308[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_contract_storage_to_pointer_with_storage.json";
val defs = mapi (define_test "0308") tests;
