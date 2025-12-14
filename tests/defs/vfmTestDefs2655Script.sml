open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2655";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_7827-6598_1456_21000_80.json";
val defs = mapi (define_test "2655") tests;
val () = export_theory_no_docs ();
