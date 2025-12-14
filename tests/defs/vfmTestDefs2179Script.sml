open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2179";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CheckCallCostOOG.json";
val defs = mapi (define_test "2179") tests;
val () = export_theory_no_docs ();
