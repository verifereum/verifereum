open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2741";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_1-2_0-0_25000_64.json";
val defs = mapi (define_test "2741") tests;
val () = export_theory_no_docs ();
