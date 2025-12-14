open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1369";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest143.json";
val defs = mapi (define_test "1369") tests;
val () = export_theory_no_docs ();
