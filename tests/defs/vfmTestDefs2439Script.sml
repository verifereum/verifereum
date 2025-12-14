open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2439";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/return1.json";
val defs = mapi (define_test "2439") tests;
val () = export_theory_no_docs ();
