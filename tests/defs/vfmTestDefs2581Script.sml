open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2581";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/dayLimitConstruction.json";
val defs = mapi (define_test "2581") tests;
val () = export_theory_no_docs ();
