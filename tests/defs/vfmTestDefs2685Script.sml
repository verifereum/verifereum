open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2685";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-2_9935_28000_128.json";
val defs = mapi (define_test "2685") tests;
val () = export_theory_no_docs ();
