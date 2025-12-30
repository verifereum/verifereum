Theory vfmTestDefs0335[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_pointer_measurements.json";
val defs = mapi (define_test "0335") tests;
