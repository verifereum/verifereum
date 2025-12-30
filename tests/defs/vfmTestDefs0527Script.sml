Theory vfmTestDefs0527[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stAttackTest/CrashingTransaction.json";
val defs = mapi (define_test "0527") tests;
