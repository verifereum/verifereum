open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1034";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/mergeTest.json";
val defs = mapi (define_test "1034") tests;
val () = export_theory_no_docs ();
