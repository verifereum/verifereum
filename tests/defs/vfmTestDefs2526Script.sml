open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2526";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/testRandomTest.json";
val defs = mapi (define_test "2526") tests;
val () = export_theory_no_docs ();
