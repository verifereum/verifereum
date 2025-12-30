Theory vfmTestDefs1053[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/TransactionCreateAutoSuicideContract.json";
val defs = mapi (define_test "1053") tests;
