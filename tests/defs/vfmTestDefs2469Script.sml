open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2469";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/dayLimitConstructionPartial.json";
val defs = mapi (define_test "2469") tests;
val () = export_theory_no_docs ();
