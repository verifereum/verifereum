Theory vfmTestDefs2539[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletExecuteUnderDailyLimit.json";
val defs = mapi (define_test "2539") tests;
