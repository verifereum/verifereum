open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1630";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest345.json";
val defs = mapi (define_test "1630") tests;
val () = export_theory_no_docs ();
