open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2353";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallRecursiveBomb0.json";
val defs = mapi (define_test "2353") tests;
val () = export_theory_no_docs ();
