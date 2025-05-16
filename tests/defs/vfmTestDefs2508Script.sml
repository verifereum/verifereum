open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2508";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletRemoveOwnerRemovePendingTransaction.json";
val defs = mapi (define_test "2508") tests;
val () = export_theory_no_docs ();
