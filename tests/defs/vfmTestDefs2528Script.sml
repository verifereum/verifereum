Theory vfmTestDefs2528[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletChangeOwnerRemovePendingTransaction.json";
val defs = mapi (define_test "2528") tests;
