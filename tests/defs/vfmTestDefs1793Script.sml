open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1793";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest624.json";
val defs = mapi (define_test "1793") tests;
val () = export_theory_no_docs ();
