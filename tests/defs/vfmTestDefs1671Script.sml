open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1671";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest42.json";
val defs = mapi (define_test "1671") tests;
val () = export_theory_no_docs ();
