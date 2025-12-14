open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2747";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_1-3_0-0_25000_80_Paris.json";
val defs = mapi (define_test "2747") tests;
val () = export_theory_no_docs ();
