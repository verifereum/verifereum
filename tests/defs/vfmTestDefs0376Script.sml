Theory vfmTestDefs0376[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_signature_s_out_of_range.json";
val defs = mapi (define_test "0376") tests;
