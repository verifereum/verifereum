Theory vfmTestDefs2529[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletChangeRequirementRemovePendingTransaction.json";
val defs = mapi (define_test "2529") tests;
