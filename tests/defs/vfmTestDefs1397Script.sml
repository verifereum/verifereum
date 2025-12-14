open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1397";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest173.json";
val defs = mapi (define_test "1397") tests;
val () = export_theory_no_docs ();
