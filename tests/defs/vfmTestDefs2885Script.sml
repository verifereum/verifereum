open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2885";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-3_1_28000_128.json";
val defs = mapi (define_test "2885") tests;
val () = export_theory_no_docs ();
