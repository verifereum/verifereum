Theory vfmTestDefs2527[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletAddOwnerRemovePendingTransaction.json";
val defs = mapi (define_test "2527") tests;
