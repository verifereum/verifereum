Theory vfmTestDefs0985[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP3607/transactionCollidingWithNonEmptyAccount_calls.json";
val defs = mapi (define_test "0985") tests;
