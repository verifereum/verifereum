open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2900";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-3_5616_28000_96_Paris.json";
val defs = mapi (define_test "2900") tests;
val () = export_theory_no_docs ();
