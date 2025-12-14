open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1607";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest58.json";
val defs = mapi (define_test "1607") tests;
val () = export_theory_no_docs ();
