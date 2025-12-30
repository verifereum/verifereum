Theory vfmTestDefs0305[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_call_to_pre_authorized_oog.json";
val defs = mapi (define_test "0305") tests;
