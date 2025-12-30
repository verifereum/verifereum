Theory vfmTestDefs2464[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/CreateMessageReverted.json";
val defs = mapi (define_test "2464") tests;
