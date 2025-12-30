Theory vfmTestDefs0320[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_eoa_init_as_pointer.json";
val defs = mapi (define_test "0320") tests;
