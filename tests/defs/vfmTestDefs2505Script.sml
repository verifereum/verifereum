Theory vfmTestDefs2505[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/dayLimitResetSpentToday.json";
val defs = mapi (define_test "2505") tests;
