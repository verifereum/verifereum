open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2828";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_1145-3932_1145-4651_25000_192.json";
val defs = mapi (define_test "2828") tests;
val () = export_theory_no_docs ();
