Theory vfmTestDefs0151[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/validation/test_sender_balance.json";
val defs = mapi (define_test "0151") tests;
