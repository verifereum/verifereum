Theory vfmTestDefs0341[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_pointer_to_precompile.json";
val defs = mapi (define_test "0341") tests;
