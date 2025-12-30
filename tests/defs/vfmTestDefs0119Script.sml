Theory vfmTestDefs0119[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/create/test_create_one_byte.json";
val defs = mapi (define_test "0119") tests;
