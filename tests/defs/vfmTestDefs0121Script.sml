Theory vfmTestDefs0121[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/create/test_create_suicide_store.json";
val defs = mapi (define_test "0121") tests;
