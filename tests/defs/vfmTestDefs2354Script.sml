open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2354";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallRecursiveBomb0_OOG_atMaxCallDepth.json";
val defs = mapi (define_test "2354") tests;
val () = export_theory_no_docs ();
