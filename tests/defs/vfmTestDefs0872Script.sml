Theory vfmTestDefs0872[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/TransactionCollisionToEmptyButCode.json";
val defs = mapi (define_test "0872") tests;
