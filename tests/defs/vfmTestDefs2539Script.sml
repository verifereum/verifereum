open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2539";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/walletExecuteUnderDailyLimit.json";
val defs = mapi (define_test "2539") tests;
val () = export_theory_no_docs ();
