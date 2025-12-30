Theory vfmTestDefs2445[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/suicideNotExistingAccount.json";
val defs = mapi (define_test "2445") tests;
