Theory vfmTestDefs0349[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_address_and_authority_warm_state_call_types.json";
val defs = mapi (define_test "0349") tests;
