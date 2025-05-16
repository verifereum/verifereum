open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1304";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest115.json";
val defs = mapi (define_test "1304") tests;
val () = export_theory_no_docs ();
