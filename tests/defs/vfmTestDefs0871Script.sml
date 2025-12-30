Theory vfmTestDefs0871[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/TransactionCollisionToEmpty2.json";
val defs = mapi (define_test "0871") tests;
