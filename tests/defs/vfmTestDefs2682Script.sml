open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2682";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/pointMulAdd2.json";
val defs = mapi (define_test "2682") tests;
val () = export_theory_no_docs ();
