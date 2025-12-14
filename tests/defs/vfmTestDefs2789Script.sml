open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2789";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-0_9935_21000_96.json";
val defs = mapi (define_test "2789") tests;
val () = export_theory_no_docs ();
