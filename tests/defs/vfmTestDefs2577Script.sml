open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2577";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-3_0_28000_128.json";
val defs = mapi (define_test "2577") tests;
val () = export_theory_no_docs ();
