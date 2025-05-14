open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1618";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest332.json";
val defs = mapi (define_test "1618") tests;
val () = export_theory_no_docs ();
