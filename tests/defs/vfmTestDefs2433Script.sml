Theory vfmTestDefs2433[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/currentAccountBalance.json";
val defs = mapi (define_test "2433") tests;
