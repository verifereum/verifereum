Theory vfmTestDefs0164[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/london/validation/test_invalid_header.json";
val defs = mapi (define_test "0164") tests;
