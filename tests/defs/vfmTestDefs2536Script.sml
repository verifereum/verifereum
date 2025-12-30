Theory vfmTestDefs2536[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletExecuteOverDailyLimitMultiOwner.json";
val defs = mapi (define_test "2536") tests;
