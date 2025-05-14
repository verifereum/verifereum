open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2798";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/pointAddTrunc.json";
val defs = mapi (define_test "2798") tests;
val () = export_theory_no_docs ();
