open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2394";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/createNameRegistratorZeroMemExpansion.json";
val defs = mapi (define_test "2394") tests;
val () = export_theory_no_docs ();
