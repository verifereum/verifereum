Theory vfmTestDefs2431[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/createNameRegistratorZeroMemExpansion.json";
val defs = mapi (define_test "2431") tests;
