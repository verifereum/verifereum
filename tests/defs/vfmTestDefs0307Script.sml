Theory vfmTestDefs0307[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_contract_create.json";
val defs = mapi (define_test "0307") tests;
