open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2673";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-2_5616_28000_128.json";
val defs = mapi (define_test "2673") tests;
val () = export_theory_no_docs ();
