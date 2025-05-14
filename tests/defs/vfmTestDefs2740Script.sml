open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2740";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_7827-6598_1456_28000_128.json";
val defs = mapi (define_test "2740") tests;
val () = export_theory_no_docs ();
