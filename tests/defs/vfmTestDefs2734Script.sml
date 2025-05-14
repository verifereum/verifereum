open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2734";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_7827-6598_0_28000_64.json";
val defs = mapi (define_test "2734") tests;
val () = export_theory_no_docs ();
