open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2810";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_0-0_0-0_25000_80.json";
val defs = mapi (define_test "2810") tests;
val () = export_theory_no_docs ();
