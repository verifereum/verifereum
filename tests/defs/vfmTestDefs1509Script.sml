open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1509";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest209.json";
val defs = mapi (define_test "1509") tests;
val () = export_theory_no_docs ();
