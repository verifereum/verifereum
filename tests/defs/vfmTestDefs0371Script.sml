Theory vfmTestDefs0371[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_to_tstore_reentry.json";
val defs = mapi (define_test "0371") tests;
