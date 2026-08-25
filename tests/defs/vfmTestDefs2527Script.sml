Theory vfmTestDefs2527[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletAddOwnerRemovePendingTransaction.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stWalletTest/walletAddOwnerRemovePendingTransaction.json");
val defs = mapi (define_test "2527") tests;
