open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2810";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_1-2_1_28000_96.json";
val defs = mapi (define_test "2810") tests;
val () = export_theory_no_docs ();
