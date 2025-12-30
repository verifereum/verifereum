Theory vfmTestDefs0315[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_delegation_replacement_call_previous_contract.json";
val defs = mapi (define_test "0315") tests;
