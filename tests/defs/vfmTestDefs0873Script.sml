Theory vfmTestDefs0873[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/TransactionCollisionToEmptyButNonce.json";
val defs = mapi (define_test "0873") tests;
