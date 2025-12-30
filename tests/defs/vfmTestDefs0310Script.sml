Theory vfmTestDefs0310[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_delegate_call_targets.json";
val defs = mapi (define_test "0310") tests;
