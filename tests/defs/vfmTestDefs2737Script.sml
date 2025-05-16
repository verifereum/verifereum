open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2737";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-0_2_28000_128.json";
val defs = mapi (define_test "2737") tests;
val () = export_theory_no_docs ();
