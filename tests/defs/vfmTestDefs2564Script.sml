open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2564";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-2_616_28000_96.json";
val defs = mapi (define_test "2564") tests;
val () = export_theory_no_docs ();
