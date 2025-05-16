open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2696";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_0-0_1-2_25000_192.json";
val defs = mapi (define_test "2696") tests;
val () = export_theory_no_docs ();
