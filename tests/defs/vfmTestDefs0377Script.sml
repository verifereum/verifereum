Theory vfmTestDefs0377[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_static_to_pointer.json";
val defs = mapi (define_test "0377") tests;
