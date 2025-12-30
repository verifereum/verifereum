Theory vfmTestDefs0115[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/constantinople/eip1014_create2/test_create2_return_data.json";
val defs = mapi (define_test "0115") tests;
