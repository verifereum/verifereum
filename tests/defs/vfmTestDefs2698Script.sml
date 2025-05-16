open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2698";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_0-0_1-3_25000_128.json";
val defs = mapi (define_test "2698") tests;
val () = export_theory_no_docs ();
