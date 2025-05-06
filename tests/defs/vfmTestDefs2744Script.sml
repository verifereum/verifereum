open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2744";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_7827-6598_2_21000_96.json";
val defs = mapi (define_test "2744") tests;
val () = export_theory_no_docs ();
