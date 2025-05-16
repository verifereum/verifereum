open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2403";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/return2.json";
val defs = mapi (define_test "2403") tests;
val () = export_theory_no_docs ();
