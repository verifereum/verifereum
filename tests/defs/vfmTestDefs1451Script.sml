open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1451";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest28.json";
val defs = mapi (define_test "1451") tests;
val () = export_theory_no_docs ();
