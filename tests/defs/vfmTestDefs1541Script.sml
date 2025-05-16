open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1541";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest372.json";
val defs = mapi (define_test "1541") tests;
val () = export_theory_no_docs ();
