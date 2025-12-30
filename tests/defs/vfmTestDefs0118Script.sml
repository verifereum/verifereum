Theory vfmTestDefs0118[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/create/test_create_deposit_oog.json";
val defs = mapi (define_test "0118") tests;
