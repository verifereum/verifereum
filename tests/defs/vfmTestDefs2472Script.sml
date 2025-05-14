open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2472";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallRecursiveBomb0_OOG_atMaxCallDepth.json";
val defs = mapi (define_test "2472") tests;
val () = export_theory_no_docs ();
