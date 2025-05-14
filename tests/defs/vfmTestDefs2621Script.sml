open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2621";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletExecuteOverDailyLimitOnlyOneOwnerNew.json";
val defs = mapi (define_test "2621") tests;
val () = export_theory_no_docs ();
