open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2787";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-3_5617_21000_128.json";
val defs = mapi (define_test "2787") tests;
val () = export_theory_no_docs ();
