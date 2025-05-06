open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2585";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/dayLimitSetDailyLimit.json";
val defs = mapi (define_test "2585") tests;
val () = export_theory_no_docs ();
