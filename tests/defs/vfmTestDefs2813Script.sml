open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2813";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_0-3_1-2_21000_128.json";
val defs = mapi (define_test "2813") tests;
val () = export_theory_no_docs ();
