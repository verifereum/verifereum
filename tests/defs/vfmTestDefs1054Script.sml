Theory vfmTestDefs1054[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/TransactionCreateRandomInitCode.json";
val defs = mapi (define_test "1054") tests;
