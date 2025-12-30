Theory vfmTestDefs0324[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_ext_code_on_self_set_code.json";
val defs = mapi (define_test "0324") tests;
