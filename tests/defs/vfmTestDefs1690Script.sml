open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1690";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest64.json";
val defs = mapi (define_test "1690") tests;
val () = export_theory_no_docs ();
