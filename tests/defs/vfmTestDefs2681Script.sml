open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2681";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/pointMulAdd.json";
val defs = mapi (define_test "2681") tests;
val () = export_theory_no_docs ();
