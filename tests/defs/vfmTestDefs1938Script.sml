open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1938";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertOnEmptyStack.json";
val defs = mapi (define_test "1938") tests;
val () = export_theory_no_docs ();
