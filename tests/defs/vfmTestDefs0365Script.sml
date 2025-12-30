Theory vfmTestDefs0365[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_to_self_destruct.json";
val defs = mapi (define_test "0365") tests;
