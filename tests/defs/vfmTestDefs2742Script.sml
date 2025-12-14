open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2742";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_1-2_1-2_21000_128.json";
val defs = mapi (define_test "2742") tests;
val () = export_theory_no_docs ();
